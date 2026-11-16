-- Prove2me | Definitions.Def_RandomCNFDeficiency_LowerBound_Supplement_Covering
-- name    : RandomCNFDeficiency_LowerBound_Supplement_Covering
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:55:56.03911+00:00
-- url     : https://prove2.me/theorems/e3bb98bb-09bd-454e-ba4d-4e9ff1943ad0
-- title:
--   Support covering and one-step resolvents $\mathrm{Resol}(F)$
-- statement:
--   A clause set $G$ **covers the $q$-element variable sets** if every set $T\subseteq[n]$ with $|T|=q$ contains the variable support $\mathrm{Vars}(C)$ of some clause $C\in G$.
--
--   For a CNF $F$ and an integer $k$, $\mathrm{Resol}(F)$ is the set of resolvents $A\vee B$ of pairs of clauses $z\vee A$ and $\neg z\vee B$ of $F$ (the pivot $z$ may carry either sign in either clause) such that both clauses have width exactly $k$ and their variable supports intersect in exactly the resolution variable $z$:
--
--   $$\mathrm{Vars}(z\vee A)\cap\mathrm{Vars}(\neg z\vee B)=\{z\}.$$
--
--   The resolvent drops $z$ and keeps every other literal of both parents, so it has width exactly $2k-2$. No tautological or iterated resolvents are included.
--
--   These objects carry the deterministic degree criterion (Lemma 4.2) and the probabilistic covering estimate (Lemma 4.6) behind the polynomial calculus upper bound of Section 4.
--
--   **Formalization Note** Clauses are the published signed clauses `Fin n → Option Bool`; the width-$k$ requirement on both parents is part of the definition, which agrees with the source for the $k$-CNFs it considers.
-- source:
--   Jonas Conneryd, STOC 2027 submission #332 (October 2026), Section 4.1, printed p. 15, PDF p. 17; Section 4.2, printed p. 17, PDF p. 19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/332.pdf

import Definitions.Def_RandomCNFDeficiency_LowerBound_Clause
set_option autoImplicit false

namespace RandomCNFDeficiency.LowerBound.Supplement

open RandomCNFDeficiency.LowerBound

/-- The clause set `G` covers the `q`-element variable sets: every `T ⊆ [n]` with `|T| = q`
contains the variable support of some clause of `G`. A CNF `F` is used through its coercion
`(F : Set (Clause n))`. -/
def CoversSets {n : ℕ} (G : Set (Clause n)) (q : ℕ) : Prop :=
  ∀ T : Finset (Fin n), T.card = q → ∃ C ∈ G, clauseSupport C ⊆ T

/-- `C₁ = z ∨ A` and `C₂ = ¬z ∨ B` (either sign of `z` on either side) are width-`k` clauses whose
supports meet exactly in the resolution variable `z`, with opposite signs on `z`. -/
def IsResolvablePair {n : ℕ} (k : ℕ) (C₁ C₂ : Clause n) (z : Fin n) : Prop :=
  clauseWidth C₁ = k ∧ clauseWidth C₂ = k ∧
    (∃ b : Bool, C₁ z = some b ∧ C₂ z = some (!b)) ∧
    clauseSupport C₁ ∩ clauseSupport C₂ = {z}

/-- The resolvent `A ∨ B` of `z ∨ A` and `¬z ∨ B`: drop `z`, keep every other literal. -/
def resolvent {n : ℕ} (C₁ C₂ : Clause n) (z : Fin n) : Clause n :=
  fun i => if i = z then none else if (C₁ i).isSome then C₁ i else C₂ i

/-- `Resol(F)`: all resolvents of pairs of width-`k` clauses of `F` whose supports intersect in
exactly the resolution variable. -/
def Resol {n : ℕ} (F : CNF n) (k : ℕ) : Set (Clause n) :=
  {R | ∃ C₁ ∈ F, ∃ C₂ ∈ F, ∃ z, IsResolvablePair k C₁ C₂ z ∧ R = resolvent C₁ C₂ z}

end RandomCNFDeficiency.LowerBound.Supplement


