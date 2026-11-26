-- Prove2me | solution 1 for Auto.aux_integral_sum_overlapContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:49:32.881586+00:00
-- url     : https://prove2.me/submissions/98411b18-150a-4c01-a44c-527f0a28f036

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
public import Theorems.Thm_Auto_aux_overlapLower_le_overlapUpper
public import Theorems.Thm_Auto_aux_overlapWidth_eq_translate_width
public import Theorems.Thm_Auto_aux_overlapContribution_eq_indicator
public import Theorems.Thm_Auto_aux_integral_indicator_Ico_const

set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace Auto
theorem _root_.solution {n : ℕ} (hn : 0 < n)
    {ε δ : ℝ} (hεδ : ε ≤ δ) (a : Fin n → aux_ZVector n → ℝ)
    (k : aux_ZVector n) (u : aux_RVector n) (N : ℕ)
    (hu : ∀ i, 0 ≤ u i ∧ u i < ε) :
    ∫ s : ℝ, ∑ q : Fin N, aux_overlapContribution ε δ a k u q.val s =
      aux_overlapWidth hn ε δ u * ∑ q : Fin N,
        ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ)) := by
  rw [MeasureTheory.integral_finsetSum]
  · calc
      ∑ q ∈ (Finset.univ : Finset (Fin N)),
          ∫ s : ℝ, aux_overlapContribution ε δ a k u q.val s =
          ∑ q ∈ (Finset.univ : Finset (Fin N)),
            (aux_overlapUpper hn ε δ u q.val - aux_overlapLower hn ε u q.val) *
              ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ)) := by
        apply Finset.sum_congr rfl
        intro q hq
        calc
          ∫ s : ℝ, aux_overlapContribution ε δ a k u q.val s =
              ∫ s : ℝ, (Ico (aux_overlapLower hn ε u q.val)
                (aux_overlapUpper hn ε δ u q.val)).indicator
                  (fun _ ↦ ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ))) s := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with s
            exact aux_overlapContribution_eq_indicator hn ε δ a k u q.val s
          _ = _ := aux_integral_indicator_Ico_const
            (aux_overlapLower_le_overlapUpper hn u q.val
              (fun i ↦ ⟨(hu i).1, (hu i).2.le⟩) hεδ)
      _ = _ := by
        simp_rw [← aux_overlapWidth_eq_translate_width hn ε δ u]
        rw [Finset.mul_sum]
  · intro q hq
    change Integrable (fun s ↦ aux_overlapContribution ε δ a k u q.val s) volume
    rw [show (fun s ↦ aux_overlapContribution ε δ a k u q.val s) =
      (fun s ↦ (Ico (aux_overlapLower hn ε u q.val)
        (aux_overlapUpper hn ε δ u q.val)).indicator
          (fun _ ↦ ∏ i, a i (aux_translateAxisInt k i (q.val : ℤ))) s) by
      funext s
      exact aux_overlapContribution_eq_indicator hn ε δ a k u q.val s]
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ico]
    exact MeasureTheory.integrableOn_const measure_Ico_lt_top.ne
end Auto
