-- Prove2me | Definitions.Def_QBFBackdoor_DQBF
-- name    : QBFBackdoor_DQBF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:10.148567+00:00
-- url     : https://prove2.me/theorems/0d26a2bb-f992-403d-88f7-98a67470f4ff
-- title:
--   $\Gamma_{\mathrm{AFF}}$ atoms and disjunctive QBF over $\Gamma_{\mathrm{AFF}}$
-- statement:
--   The class $\Gamma_{\mathrm{AFF}}\subseteq\mathrm{AFF}$ consists of conjunctions of the atoms
--
--   $$
--   (x)=1,\qquad (x)=0,\qquad (x\oplus y)=0,
--   $$
--
--   written $(x)$, $(\neg x)$ and $(x=y)$. An assignment satisfies a conjunction if it satisfies every atom; the empty conjunction is $\top$.
--
--   A **disjunctive QBF over $\Gamma_{\mathrm{AFF}}$** is a formula $Q.(\phi_1\vee\cdots\vee\phi_q)$ with a quantifier prefix $Q$ on $x_1,\dots,x_n$ and disjuncts $\phi_1,\dots,\phi_q\in\Gamma_{\mathrm{AFF}}$; it belongs to $q$-Disjunct-QBF$(\Gamma_{\mathrm{AFF}})$. The empty disjunction is $\bot$. Its truth is the truth of $Q.F$ for the matrix $F=\phi_1\vee\cdots\vee\phi_q$, and its atom count $m$ is the total number of atoms of the disjuncts.
--
--   These formulas are the intermediate problem of the lower-bound proof: Lemma 5.4 shows that they are PSPACE-complete with unboundedly many disjuncts, and squishing reduces the number of disjuncts to four.
--
--   **Formalization Note** Atoms are the inductive type `GAtom n` (`unit x b` is $(x)=b$, `eq x y` is $(x=y)$). Disjuncts are lists, kept as indexed slots with duplicates, as on p.16. An instance bundles $n$ with the formula (`DQBFInst`).
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §5.2, p.23 (ΓAFF); §3.2, p.16 (q-Disjunct-QBF(C)); §3.2, p.15 (truth)

import Mathlib
import Definitions.Def_QBFBackdoor_PrefixHolds

namespace QBFBackdoor

/-- **The atoms of `Γ_AFF`.** Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki,
*Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version, sha256 3ea1662e…),
§5.2, p.23: "ΓAFF ⊆ AFF which contains formulas with atoms of the form (x) = 0, (x) = 1 and
(x ⊕ y) = 0 … we will use the following shorthands (¬x), (x) and (x = y)".

`unit x b` is the atom `(x) = b`, so `unit x true` is `(x)` and `unit x false` is `(¬x)`;
`eq x y` is `(x ⊕ y) = 0`, i.e. `(x = y)`. Variables are `Fin n`. -/
inductive GAtom (n : ℕ) where
  | unit (x : Fin n) (b : Bool)
  | eq (x y : Fin n)
  deriving DecidableEq

/-- An assignment `a` satisfies a `Γ_AFF` atom. -/
def GAtom.Sat {n : ℕ} : GAtom n → (Fin n → Bool) → Prop
  | .unit x b, a => a x = b
  | .eq x y, a => a x = a y

/-- An assignment satisfies a conjunction of `Γ_AFF` atoms (a formula in `Γ_AFF`); the empty
conjunction is `⊤` (p.16). -/
def SatAll {n : ℕ} (ϕ : List (GAtom n)) (a : Fin n → Bool) : Prop :=
  ∀ C ∈ ϕ, C.Sat a

/-- **Disjunctive QBF over `Γ_AFF`** (§3.2, p.16): "for a class of formulas C and a positive
integer q ∈ Z+, let q-Disjunct-C be the class of formulas ϕ such that ϕ = ϕ1 ∨ . . . ∨ ϕq and let
q-Disjunct-QBF(C) be the class of QBF formulas, where the matrix is in q-Disjunct-C, for some
ϕ1, . . . , ϕq ∈ C."

A prefix `q` over `Fin n` (`true` = ∃, variables quantified in index order) and the disjuncts
`disj`, each a list of `Γ_AFF` atoms read as a conjunction. The instance is in
`q`-Disjunct-QBF(ΓAFF) when `disj.length = q`.

**Formalization Note** Disjuncts are indexed slots and duplicates are retained, as on p.16
("we regard them as indexed slots and retain duplicates"). -/
structure DQBF (n : ℕ) where
  q : Fin n → Bool
  disj : List (List (GAtom n))

/-- The disjunctive matrix `ϕ₁ ∨ … ∨ ϕ_q` is true under `a`; the empty disjunction is `⊥`
(p.16). -/
def DQBF.Sat {n : ℕ} (Φ : DQBF n) (a : Fin n → Bool) : Prop :=
  ∃ ϕ ∈ Φ.disj, SatAll ϕ a

/-- Truth of the disjunctive QBF (§3.2, p.15). -/
def DQBF.holds {n : ℕ} (Φ : DQBF n) : Prop :=
  PrefixHolds Φ.q Φ.Sat

/-- The number of atoms of the matrix, summed over the disjuncts (the `m` of Lemma 5.7). -/
def DQBF.atomCount {n : ℕ} (Φ : DQBF n) : ℕ :=
  (Φ.disj.map List.length).sum

/-- An instance of Disjunct-QBF(ΓAFF) with its number of variables. -/
structure DQBFInst where
  n : ℕ
  Φ : DQBF n

end QBFBackdoor


