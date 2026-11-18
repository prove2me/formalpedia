-- Prove2me | Definitions.Def_Kyprianou_Ch09_Pathwise
-- name    : Kyprianou_Ch09_Pathwise
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:12:58.962096+00:00
-- url     : https://prove2.me/theorems/dc9882f0-8514-4f9d-a943-4c05ed21203e
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner Pathwise
-- statement:
--   Pathwise process and path-limit foundations for fluctuation and stopping arguments. This source Definition module provides the actual declarations: driftMinus. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- A bounded-variation negative-jump path with positive drift. -/
def driftMinus (d : ℝ) (S : ℝ → ℝ) (t : ℝ) : ℝ := d * t - S t

/-- A nonnegative residual keeps the process below its drift envelope. -/
theorem driftMinus_le (d t : ℝ) (S : ℝ → ℝ)
    (hS : 0 ≤ S t) : driftMinus d S t ≤ d * t := by
  unfold driftMinus
  linarith

/-- Full physical-grid bound for every earlier time. -/
theorem driftMinus_prefix_le (d t : ℝ) (S : ℝ → ℝ)
    (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hS : ∀ s, 0 ≤ s → 0 ≤ S s) :
    ∀ s ∈ Set.Icc (0 : ℝ) t, driftMinus d S s ≤ d * t := by
  intro s hs
  have hbound := driftMinus_le d s S (hS s hs.1)
  have hmul := mul_le_mul_of_nonneg_left hs.2 hd
  linarith

/-- Discounted running maximum is bounded by immediate stopping payoff. -/
theorem discounted_max_bound (q d x t M : ℝ)
    (hq : d ≤ q) (hd : 0 ≤ d) (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hM : M ≤ d * t) :
    Real.exp (-q * t + max x M) ≤ Real.exp x := by
  have hqt := mul_le_mul_of_nonneg_right hq ht
  have hdt : 0 ≤ d * t := mul_nonneg hd ht
  have hmax : max x M ≤ x + d * t := by
    apply max_le
    · linarith
    · linarith
  apply Real.exp_le_exp.mpr
  linarith

/-- Two corrected penalty regimes are disjoint and exhaustive. -/
theorem penalty_regimes_partition (δ C : ℝ) (hδ : 0 < δ) :
    (C ≤ δ ∨ (0 < δ ∧ δ < C)) ∧ ¬ (C ≤ δ ∧ δ < C) := by
  constructor
  · rcases lt_or_ge δ C with h | h
    · exact Or.inr ⟨hδ, h⟩
    · exact Or.inl h
  · intro h
    exact not_lt_of_ge h.1 h.2

end Kyprianou.Ch09.B1


