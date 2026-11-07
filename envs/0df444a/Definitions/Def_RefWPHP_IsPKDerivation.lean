-- Prove2me | Definitions.Def_RefWPHP_IsPKDerivation
-- name    : RefWPHP_IsPKDerivation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:00:17.866199+00:00
-- url     : https://prove2.me/theorems/dc23c5a8-a1ac-4f32-afdc-3e0e9fc6d9d8
-- title:
--   The calculus PK: cedents, inference rules, PK$_d$-derivations and refutations from a set of cedents, derivation size
-- statement:
--   A **cedent** is a sequence of formulas, read as their disjunction; the empty cedent is $\bot$. Fix a set $\Phi$ of cedents. A **PK$_d$-derivation from $\Phi$** is a sequence of cedents in which every formula has depth at most $d$ and each cedent is obtained in one of these ways:
--
--   1. it belongs to $\Phi$;
--   2. (Atomic LEM) it is $p, \neg p$;
--   3. ($\wedge$-Intro) it is $\bigwedge_i \varphi_i, \Gamma$, and $\varphi_i, \Gamma$ occurs earlier for every $i$;
--   4. ($\vee$-Intro) it is $\bigvee_i \varphi_i, \Gamma$, and $\Gamma, \varphi_1, \dots, \varphi_k$ occurs earlier;
--   5. (Weak) it contains every formula of an earlier cedent;
--   6. (Cut) it is $\Gamma$, and either $\varphi, \Gamma$ and $\neg\varphi, \Gamma$ occur earlier, or $\varphi_1 \wedge \dots \wedge \varphi_k, \Gamma$ and $\Gamma, \neg\varphi_1, \dots, \neg\varphi_k$ occur earlier.
--
--   A derivation of $\Gamma$ ends in $\Gamma$, and a **refutation** of $\Phi$ is a derivation of the empty cedent. The **size** of a derivation is the sum over its lines of one plus the sizes of the line's formulas.
--
--   This is the proof system of Theorem 3.2. PK$_0$ is Resolution, because every axiom of a CNF is a cedent of literals and the single-formula Cut on a literal is the Resolution rule.
--
--   **Formalization Note** The paper displays binary introduction rules on unbounded fan-in formulas and uses "repeated $\wedge$-introduction" as one step; the rules here are $n$-ary, so $\top$ is derived from nothing. Weakening to any list containing the premise also performs exchange and contraction. Derivations are dag-like: any earlier line may be used any number of times. The paper's size is the length of a binary string encoding the derivation (p.15), which differs from this count by at most a logarithmic factor in the number of variables; the $+1$ per line makes the length at most the size, as on p.14.
-- source:
--   Arteche, Resolution Lower Bounds versus the Weak Pigeonhole Principle, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, pp.14–15 (PDF pp.16–17)

import Mathlib
import Definitions.Def_RefWPHP_PKFormula

namespace RefWPHP

open PKFormula

/-- A cedent, p.14: "a sequence of formulas, separated by commas, interpreted as their
disjunction". The empty cedent is ⊥. -/
abbrev Cedent (V : Type) : Type := List (PKFormula V)

/-- One inference of the calculus PK of N. Arteche, *Resolution Lower Bounds versus the Weak
Pigeonhole Principle*, STOC 2027 submission (held manuscript, sha256 ee75d7f1…), §2.1.2, pp.14–15,
in a derivation from a set `Φ` of cedents: `PKStep Φ prev Γ` says that `Γ` is in `Φ` or follows by
one rule from cedents in `prev` (the earlier lines).

* `hyp`: `Γ ∈ Φ`;
* `lem` (Atomic LEM): `p, ¬p`;
* `andI` (∧-Intro): from `φ, Γ` for every `φ ∈ φs`, infer `⋀φs, Γ`;
* `orI` (∨-Intro): from `Γ, φs`, infer `⋁φs, Γ`;
* `weak` (Weak): from `Γ`, infer any `Δ` containing every formula of `Γ`;
* `cut1` (Cut with `m = 1`): from `φ, Γ` and `¬φ, Γ`, infer `Γ`;
* `cutAnd` (Cut): from `Γ, φ₁ ∧ ⋯ ∧ φₘ` and `Γ, ¬φ₁, …, ¬φₘ`, infer `Γ`.

**Formalization Note.** The paper displays binary ∧/∨-Intro on unbounded fan-in formulas and
uses "repeated ∧-introduction" as one step; the rules here are n-ary (`and []`, i.e. ⊤, is derived
from nothing). Cedents are lists; weakening is to any list containing the premise's formulas, so
it also performs exchange and contraction. Cut has two instances: on a single formula, and on a
conjunction whose conjuncts are negated separately. -/
inductive PKStep {V : Type} (Φ : Set (Cedent V)) (prev : List (Cedent V)) : Cedent V → Prop
  | hyp (Γ : Cedent V) : Γ ∈ Φ → PKStep Φ prev Γ
  | lem (v : V) : PKStep Φ prev [pos v, neg v]
  | andI (φs : List (PKFormula V)) (Γ : Cedent V) :
      (∀ φ ∈ φs, (φ :: Γ) ∈ prev) → PKStep Φ prev (and φs :: Γ)
  | orI (φs : List (PKFormula V)) (Γ : Cedent V) :
      (Γ ++ φs) ∈ prev → PKStep Φ prev (or φs :: Γ)
  | weak (Γ Δ : Cedent V) : Γ ∈ prev → Γ ⊆ Δ → PKStep Φ prev Δ
  | cut1 (φ : PKFormula V) (Γ : Cedent V) :
      (φ :: Γ) ∈ prev → (dual φ :: Γ) ∈ prev → PKStep Φ prev Γ
  | cutAnd (φs : List (PKFormula V)) (Γ : Cedent V) :
      (and φs :: Γ) ∈ prev → (Γ ++ φs.map dual) ∈ prev → PKStep Φ prev Γ

/-- A PK_d-derivation from `Φ`, pp.14–15 (dag-like): every line is in `Φ` or follows by one rule
from earlier lines (any earlier line, any number of times), and "every formula in a cedent has
depth at most `d`" (p.15). -/
def IsPKDerivation {V : Type} (d : ℕ) (Φ : Set (Cedent V)) (ρ : List (Cedent V)) : Prop :=
  ∀ (i : ℕ) (h : i < ρ.length),
    PKStep Φ (ρ.take i) (ρ[i]'h) ∧ ∀ φ ∈ ρ[i]'h, depth φ ≤ d

/-- A PK_d-derivation of the cedent `Γ` from `Φ`: a derivation "ending in Γ" (p.15). -/
def IsPKDerivationOf {V : Type} (d : ℕ) (Φ : Set (Cedent V)) (ρ : List (Cedent V))
    (Γ : Cedent V) : Prop :=
  IsPKDerivation d Φ ρ ∧ ρ.getLast? = some Γ

/-- A PK_d-refutation of `Φ`: a PK_d-derivation of the empty cedent ⊥ from `Φ` (p.15). -/
def IsPKRefutation {V : Type} (d : ℕ) (Φ : Set (Cedent V)) (ρ : List (Cedent V)) : Prop :=
  IsPKDerivationOf d Φ ρ []

/-- The size of a derivation: the sum over its lines of one plus the sizes of the line's formulas.

**Formalization Note.** The paper's size is the length of a binary string encoding the derivation
(p.15). Symbol count differs from it by at most a logarithmic factor in the number of variables, and
the `+1` per line makes the length of a derivation at most its size, as for Resolution (p.14). -/
def derivSize {V : Type} (ρ : List (Cedent V)) : ℕ :=
  (ρ.map fun Γ => 1 + (Γ.map PKFormula.size).sum).sum

end RefWPHP


