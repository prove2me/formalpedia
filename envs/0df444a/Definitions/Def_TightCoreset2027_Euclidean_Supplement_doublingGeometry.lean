-- Prove2me | Definitions.Def_TightCoreset2027_Euclidean_Supplement_doublingGeometry
-- name    : TightCoreset2027_Euclidean_Supplement_doublingGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:08:08.6202+00:00
-- url     : https://prove2.me/theorems/f5a81299-7f7f-442b-a8d3-fedf291ca305
-- title:
--   Ambient closed-ball doubling bounds and finite-space dimension
-- statement:
--   Let E be a metric space. It has doubling covering constant at most B if every closed ball of radius r>0 is covered by a finite collection of at most B closed balls of radius r/2, with all covering centers in E. Its doubling dimension is at most a real number D when
--
--   $$\forall x\in E\ \forall r>0\ \exists T\subseteq E\text{ finite}:\quad |T|\le 2^D,\qquad B(x,r)\subseteq\bigcup_{c\in T}B(c,r/2).$$
--
--   For finite E, define its actual dimension to be log₂ λ(E), where λ(E) is the least positive integer covering constant. The all-points cover proves that this least integer exists. Empty and one-point spaces have λ=1 and dimension zero. This definition is never applied to an infinite non-doubling space.
--
--   The general covering predicate places no finiteness, compactness, completeness or dimension-floor condition on the ambient space. The finite-space dimension is used only for the two-sided dimension comparison in Lemma 3.1. Closed balls agree with the radius-two/radius-one argument on printed p. 23 / PDF p. 25.
-- source:
--   Junqiu Hu, Lingxiao Huang, Jian Li, Baoduo Xu, STOC 2027 submission #879 (October 2026), §1 doubling-dimension convention and §3.2 / Lemma 3.3, printed p. 1, 23 / PDF p. 3, 25; canonical source.pdf SHA256 9c247b18d4e2080420cb421dad0fe6c53b99885cef599b8f8e3cd8d639e13d5f.

import Mathlib
set_option autoImplicit false

namespace TightCoreset2027.Euclidean.Supplement

/-- Ambient closed-ball doubling condition, with covering centers in the entire space. -/
def HasDoublingConstant (E : Type*) [MetricSpace E] (B : ℝ) : Prop :=
  ∀ x : E, ∀ r : ℝ, 0 < r → ∃ T : Finset E,
    (T.card : ℝ) ≤ B ∧
    ∀ y : E, dist y x ≤ r → ∃ c ∈ T, dist y c ≤ r / 2

/-- Dimension at most a real exponent, without an infimum or a dimension floor. -/
def HasDoublingDimensionAtMost (E : Type*) [MetricSpace E] (D : ℝ) : Prop :=
  HasDoublingConstant E (Real.rpow 2 D)

/-- The attained least positive integer covering constant of a finite metric space.
The all-points cover supplies the existence required by Nat.find, including the empty space. -/
noncomputable def finiteDoublingConstant (E : Type*) [MetricSpace E] [Fintype E] : ℕ := by
  classical
  exact Nat.find (show ∃ N : ℕ, 1 ≤ N ∧ HasDoublingConstant E (N : ℝ) from by
    classical
    refine ⟨max 1 (Fintype.card E), le_max_left _ _, ?_⟩
    intro x r hr
    refine ⟨Finset.univ, ?_, ?_⟩
    · simp only [Finset.card_univ]
      exact_mod_cast le_max_right 1 (Fintype.card E)
    · intro y _
      exact ⟨y, Finset.mem_univ y, by simpa using (le_of_lt (half_pos hr))⟩)

/-- Actual finite-space doubling dimension; empty and one-point spaces have dimension zero. -/
noncomputable def finiteDoublingDimension (E : Type*) [MetricSpace E] [Fintype E] : ℝ :=
  Real.log (finiteDoublingConstant E : ℝ) / Real.log 2

end TightCoreset2027.Euclidean.Supplement


