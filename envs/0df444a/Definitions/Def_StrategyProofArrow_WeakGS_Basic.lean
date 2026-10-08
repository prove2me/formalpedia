-- Prove2me | Definitions.Def_StrategyProofArrow_WeakGS_Basic
-- name    : StrategyProofArrow_WeakGS_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:49:38.488355+00:00
-- url     : https://prove2.me/theorems/804c2751-4764-4f17-b3be-9590a8948b91
-- title:
--   Weak and strong orders, voting procedures, strategy-proofness, dictatorship, (regular) tie-breaking functions
-- statement:
--   A committee consists of a finite set $I_n$ of $n$ individuals who must select a single alternative from a finite set $S_m$ of $m$ alternatives. This file fixes the vocabulary of §2, §3 and §6 of Satterthwaite's paper, with indifference admissible on ballots.
--
--   1. **Weak orders.** A *weak order* $R$ on $S_m$ is a complete (hence reflexive) and transitive relation; $x\,R\,y$ reads "$x$ is preferred or indifferent to $y$". The set of weak orders is $\pi_m$, and $\pi_m^n$ is the set of ballot sets $B=(B_1,\dots,B_n)$. Strict preference is $x\,\bar R\,y$ iff $x\,R\,y$ and not $y\,R\,x$.
--   2. **Strong orders.** A weak order is *strong* if it has no indifference between distinct alternatives: $x\,R\,y$ and $y\,R\,x$ imply $x=y$. The strong orders form $\rho_m\subseteq\pi_m$, and $\rho_m^n$ is the set of strict ballot sets.
--   3. **Voting procedures.** A *voting procedure* is a map $v:\pi_m^n\to S_m$; its range is $T_p=v(\pi_m^n)$, with $p=|T_p|$. A *strict voting procedure* is a map $\nu:\rho_m^n\to S_m$.
--   4. **Strategy-proofness.** $v$ is *strategy-proof* if there are no $B\in\pi_m^n$, individual $i$ and ballot $B_i'\in\pi_m$ with
--   $$v(B_1,\dots,B_i',\dots,B_n)\;\bar B_i\;v(B_1,\dots,B_i,\dots,B_n).$$
--   For a strict voting procedure, the same with $B\in\rho_m^n$ and $B_i'\in\rho_m$.
--   5. **Dictatorship.** $v$ is *dictatorial* if some individual $i$ exists such that for every $B\in\pi_m^n$ the chosen alternative $v(B)$ is among the $B_i$-maximal elements of the range: $v(B)\,B_i\,y$ for all $y\in T_p$. The same notion with $\rho_m^n$ in place of $\pi_m^n$ applies to strict voting procedures.
--   6. **Tie-breaking functions.** A *tie-breaking function* is a map $\alpha:\pi_m^n\to\rho_m^n$ such that, writing $C=\alpha(B)$, every strict preference is kept: $x\,\bar B_i\,y$ implies $x\,\bar C_i\,y$ for all $x,y$ and all $i$. A tie-breaking function $\gamma$ is *regular* if there are strong orders $Q=(Q_1,\dots,Q_n)\in\rho_m^n$ such that whenever $x\,B_i\,y$ and $y\,B_i\,x$, we have $x\,\bar C_i\,y$ iff $x\,\bar Q_i\,y$, where $C=\gamma(B)$.
--   7. **Regular voting procedures.** $v$ is *regular* if $v(B)=\nu[\gamma(B)]$ for all $B\in\pi_m^n$ for some strict voting procedure $\nu$ and some regular tie-breaking function $\gamma$.
--
--   These are the objects of Theorem 1′, the extension of the Gibbard–Satterthwaite theorem to ballots with indifference, and of Lemma 9, which decomposes strategy-proof voting procedures into a tie-breaking function followed by a strict strategy-proof voting procedure.
--
--   **Formalization Note** A weak order is the structure `WeakOrder A` (relation `rel`, completeness, transitivity); strong orders are the subtype `StrongOrder A` of weak orders satisfying `IsStrong`, taken from the shared module `StrategyProofArrow.Correspondence` (whose `WeakOrder` structure has the same three fields as this file's `WeakOrder`, so a strong ballot carries a weak order with the same relation; strict preference on it is `.1.strict`). Ballot sets are functions `ι → WeakOrder A` (`WeakProfile`) and `ι → StrongOrder A` (`StrongProfile`); voting procedures are total functions on these types, so every input is an admissible ballot set and the range $T_p$ is `Set.range v`. The substituted ballot set $(B_1,\dots,B_i',\dots,B_n)$ is `Function.update B i b`. The paper defines dictatorship through a function $f^i_T(B)$ that selects, with some tie-break, a $B_i$-maximal element of $T_p$ and leaves the tie-break unspecified; we state the equivalent condition that $v(B)$ is $B_i$-maximal in $T_p$. The paper's tie-breaking condition has two clauses ($x\,\bar B_i\,y\Rightarrow x\,\bar C_i\,y$ and $y\,\bar B_i\,x\Rightarrow y\,\bar C_i\,x$), which are the same condition with $x,y$ renamed; we state it once for all $x,y$. The value $\alpha(B)_i$ may depend on the whole ballot set $B$. The paper's remark that a regular tie-breaking function decomposes into components $\gamma_i(B_i)$ is a consequence of the definition and is not built in.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), §2, pp. 6–9 (π_m, ρ_m, voting procedures, display (1), Restriction D); §3, p. 10 (dictatorial, f^i_T); §6, pp. 38–39 (tie-breaking functions, regular tie-breaking functions, regular voting procedures, display (33))

import Mathlib
import Definitions.Def_StrategyProofArrow_Correspondence_Basic

/-!
# Weak-order ballots, strategy-proofness, dictatorship and tie-breaking functions
(Satterthwaite, Northwestern Discussion Paper No. 122, rev. Dec. 12, 1974, §2 pp. 6–9, §3 p. 10,
§6 pp. 38–39)
-/

namespace StrategyProofArrow.WeakGS

/-- A **weak order** on the alternative set `A` (the paper's `π_m`, p. 6): a relation `rel`, where
`rel x y` reads "`x` is preferred or indifferent to `y`", that is complete (hence reflexive) and
transitive. -/
structure WeakOrder (A : Type*) where
  /-- `rel x y`: `x` is preferred or indifferent to `y` (the paper's `x B_i y`). -/
  rel : A → A → Prop
  /-- Completeness: `x R y` or `y R x` for all `x, y` (in particular `R` is reflexive). -/
  total : ∀ x y : A, rel x y ∨ rel y x
  /-- Transitivity. -/
  trans : ∀ x y z : A, rel x y → rel y z → rel x z

variable {ι A : Type*}

/-- Strict preference `x R̄ y` (p. 6): `x R y` and not `y R x`. -/
def WeakOrder.strict (R : WeakOrder A) (x y : A) : Prop :=
  R.rel x y ∧ ¬ R.rel y x

/-- A weak order is a **strong order** (an element of `ρ_m`, p. 8) if it has no indifference between
distinct alternatives. -/
def WeakOrder.IsStrong (R : WeakOrder A) : Prop :=
  ∀ x y : A, R.rel x y → R.rel y x → x = y

/-- Ballot sets (and preference sets) with indifference admissible: `π^n_m` (p. 6). -/
abbrev WeakProfile (ι A : Type*) := ι → WeakOrder A

/-- A **voting procedure** `v^{nm}` (p. 6) is a single-valued map from `π^n_m` to `S_m`, i.e. a
function `WeakProfile ι A → A`; its range `T_p` is `Set.range v`. A **strict voting procedure**
(pp. 8–9) is a function `StrongProfile ι A → A` on `ρ^n_m`. -/
abbrev VotingProcedure (ι A : Type*) := WeakProfile ι A → A

/-- A strict voting procedure: domain `ρ^n_m` (pp. 8–9). -/
abbrev StrictVotingProcedure (ι A : Type*) := StrategyProofArrow.Correspondence.StrongProfile ι A → A

/-- **Strategy-proofness** (p. 7, display (1)): no individual `i`, at no ballot set `B ∈ π^n_m`, can
substitute some ballot `B'_i ∈ π_m` for `B_i` and obtain an outcome strictly better by the standard
of the original ballot `B_i`. -/
def StrategyProof [DecidableEq ι] (v : VotingProcedure ι A) : Prop :=
  ∀ (B : WeakProfile ι A) (i : ι) (b : WeakOrder A),
    ¬ (B i).strict (v (Function.update B i b)) (v B)

/-- Strategy-proofness of a strict voting procedure (pp. 8–9): ballot sets and the substituted
ballot are strong orders. -/
def StrictStrategyProof [DecidableEq ι] (ν : StrictVotingProcedure ι A) : Prop :=
  ∀ (C : StrategyProofArrow.Correspondence.StrongProfile ι A) (i : ι) (c : StrategyProofArrow.Correspondence.StrongOrder A),
    ¬ (C i).1.strict (ν (Function.update C i c)) (ν C)

/-- **Dictatorial** (p. 10): some individual `i` exists such that at every ballot set `B ∈ π^n_m`
the chosen alternative `v(B)` (which lies in the range `T_p`) is ranked by `B_i` at least as high as
every element of `T_p`, i.e. `v(B) = f^i_T(B)` for a single-valued selection `f^i_T(B)` from `i`'s
`B_i`-maximal elements of `T_p`. The tie-breaking inside that selection is left free, as on p. 10. -/
def Dictatorial (v : VotingProcedure ι A) : Prop :=
  ∃ i : ι, ∀ B : WeakProfile ι A, ∀ y ∈ Set.range v, (B i).rel (v B) y

/-- **Dictatorial** for a strict voting procedure (p. 10 with `ρ^n_m` for `π^n_m`): some `i` always
obtains its most preferred element of the range `T_p`. -/
def StrictDictatorial (ν : StrictVotingProcedure ι A) : Prop :=
  ∃ i : ι, ∀ C : StrategyProofArrow.Correspondence.StrongProfile ι A, ∀ y ∈ Set.range ν, (C i).1.rel (ν C) y

/-- A **tie-breaking function** (p. 38): a map `α : π^n_m → ρ^n_m` such that, for every `B`, every
`i` and all `x, y`, a strict preference `x B̄_i y` is kept: `x C̄_i y` where `C = α(B)`. (The paper's
second clause, `y B̄_i x ⇒ y C̄_i x`, is the same condition with `x, y` renamed.) `α(B)_i` may depend
on the whole ballot set `B`. -/
def IsTieBreaking (α : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A) : Prop :=
  ∀ (B : WeakProfile ι A) (i : ι) (x y : A), (B i).strict x y → (α B i).1.strict x y

/-- A **regular tie-breaking function** (p. 38): a tie-breaking function `γ` for which strong orders
`Q = (Q_1, …, Q_n) ∈ ρ^n_m` exist such that whenever `x B_i y` and `y B_i x`, `x C̄_i y` iff
`x Q̄_i y`, where `C = γ(B)`. -/
def IsRegularTieBreaking (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A) : Prop :=
  IsTieBreaking γ ∧
    ∃ Q : StrategyProofArrow.Correspondence.StrongProfile ι A, ∀ (B : WeakProfile ι A) (i : ι) (x y : A),
      (B i).rel x y → (B i).rel y x → ((γ B i).1.strict x y ↔ (Q i).1.strict x y)

/-- A **regular voting procedure** (p. 39, display (33)): `v(B) = ν[γ(B)]` for all `B ∈ π^n_m`, for
some strict voting procedure `ν` and some regular tie-breaking function `γ`. -/
def IsRegularVotingProcedure (v : VotingProcedure ι A) : Prop :=
  ∃ (ν : StrictVotingProcedure ι A) (γ : WeakProfile ι A → StrategyProofArrow.Correspondence.StrongProfile ι A),
    IsRegularTieBreaking γ ∧ ∀ B : WeakProfile ι A, v B = ν (γ B)

end StrategyProofArrow.WeakGS


