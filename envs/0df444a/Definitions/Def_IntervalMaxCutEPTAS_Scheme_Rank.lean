-- Prove2me | Definitions.Def_IntervalMaxCutEPTAS_Scheme_Rank
-- name    : IntervalMaxCutEPTAS_Scheme_Rank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:28.213298+00:00
-- url     : https://prove2.me/theorems/acec05f8-7c26-48f0-b173-04e3f3ab09d1
-- title:
--   Rank representations and admissible endpoint orders (§4.1)
-- statement:
--   A **rank representation** of a graph on $\{0,\dots,n-1\}$ has natural-number endpoints $\ell_v<r_v$ such that the $2n$ endpoints are the distinct integers $1,\dots,2n$.
--
--   For an interval representation $I$, an **admissible order** is an assignment of positions $1,\dots,2n$ to the $2n$ endpoints, injective, that sorts the endpoints by value and, among endpoints of equal value, places every left endpoint before every right endpoint; all remaining ties are broken arbitrarily. A rank representation $\rho$ is a **ranking of** $I$ if its endpoint map is such an admissible order. This is the replacement of coordinates performed at the start of §4.1, for every choice of tie-breaking.
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §4.1 (Rank coordinates), PDF p. 15 (printed p. 14)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Graph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-! # Rank coordinates (§4.1) -/

/-- The endpoint map of a pair of integer arrays: `inl v ↦ l v`, `inr v ↦ r v`. -/
def endsOf {n : ℕ} (l r : Fin n → ℕ) : Fin n ⊕ Fin n → ℕ := Sum.elim l r

/-- A rank representation (§4.1, "From now on we use this representation"): the `2n` endpoints are
the distinct integers `1, …, 2n`, and `l v < r v` for every vertex. -/
structure RankRep (n : ℕ) where
  l : Fin n → ℕ
  r : Fin n → ℕ
  inj : Function.Injective (endsOf l r)
  range : ∀ a, 1 ≤ endsOf l r a ∧ endsOf l r a ≤ 2 * n
  lt : ∀ v, l v < r v

/-- The rank representation as an interval representation with natural-number endpoints. -/
def RankRep.toRep {n : ℕ} (ρ : RankRep n) : Rep ℕ n := ⟨ρ.l, ρ.r, fun v => (ρ.lt v).le⟩

/-- The graph of a rank representation. -/
abbrev RankRep.graph {n : ℕ} (ρ : RankRep n) : SimpleGraph (Fin n) := ρ.toRep.graph

/-- The endpoints of a rank representation. -/
def RankRep.ends {n : ℕ} (ρ : RankRep n) : Fin n ⊕ Fin n → ℕ := endsOf ρ.l ρ.r

/-- `pos` assigns to the `2n` endpoints of `I` their positions `1, …, 2n` in a sorted order that,
among endpoints of equal value, places every left endpoint before every right endpoint, the
remaining ties being broken arbitrarily (§4.1). -/
def AdmissibleOrder {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n)
    (pos : Fin n ⊕ Fin n → ℕ) : Prop :=
  (∀ a, 1 ≤ pos a ∧ pos a ≤ 2 * n) ∧ Function.Injective pos ∧
  (∀ a b, I.ends a < I.ends b → pos a < pos b) ∧
  (∀ u v, I.l u = I.r v → pos (Sum.inl u) < pos (Sum.inr v))

/-- `ρ` is the rank representation obtained from `I` by replacing each endpoint by its position in
an admissible sorted order. -/
def IsRankingOf {R : Type} [LinearOrder R] {n : ℕ} (I : Rep R n) (ρ : RankRep n) : Prop :=
  AdmissibleOrder I ρ.ends

end IntervalMaxCutEPTAS.Scheme


