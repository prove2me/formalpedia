-- Prove2me | Definitions.Def_SourceProof_ed1669131e7bfacd70789378
-- name    : SourceProof_ed1669131e7bfacd70789378
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T15:12:15.085681+00:00
-- url     : https://prove2.me/theorems/91e71fb3-5893-4196-b76f-2b56bb95089a
-- title:
--   LevyStochCalc source module: SourceProof_ed1669131e7bfacd70789378
-- statement:
--   The original source theorem `ProbabilityTheory.constL_lt_top` comes from the `BrownianMotion.Continuity.KolmogorovChentsovInequality` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F000
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

theorem _root_.Prove2MeSourceProof.h_ed1669131e7bfacd70789378 (hT : Metric.ediam U < ∞)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β U < ∞ := by
  have hq_pos : 0 < q := lt_trans hd_pos hdq_lt
  have hC : ProbabilityTheory.Cp d p q ≠ ⊤ := by
    unfold ProbabilityTheory.Cp
    apply max_ne_top <;> apply ENNReal.div_ne_top (by norm_num)
    · apply ne_of_gt
      refine ENNReal.rpow_pos ?_ (by finiteness)
      exact tsub_pos_of_lt (ENNReal.one_lt_rpow (by norm_num) (by bound))
    · exact ne_of_gt <| tsub_pos_of_lt (ENNReal.one_lt_rpow (by norm_num) (by bound))
  have hC_pos : 0 < ProbabilityTheory.Cp d p q := by
    unfold ProbabilityTheory.Cp
    apply lt_max_of_lt_right (ENNReal.div_pos (by norm_num) (by finiteness))
  apply ENNReal.mul_lt_top (by finiteness)
  conv =>
    enter [1, 1, _]
    rw [← (ENNReal.ofReal_toReal_eq_iff (a := _ * _)).mpr (by finiteness),
      ENNReal.ofReal_eq_coe_nnreal (by positivity)]
  rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
  apply summable_of_ratio_test_tendsto_lt_one (l := 2 ^ (β * p - (q - d)))
  · apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    simp [← lt_div_iff₀, hp_pos, hβ_lt]
  · filter_upwards with k
    apply ne_of_gt
    simp only [ENNReal.toReal_mul, NNReal.coe_mk]
    apply mul_pos <;> refine ENNReal.toReal_pos_iff.mpr ⟨?_, by finiteness⟩
    · exact ENNReal.rpow_pos (by norm_num) (by norm_num)
    · positivity
  simp only [Nat.cast_add, Nat.cast_one, ENNReal.toReal_mul, NNReal.coe_mk, norm_mul,
    Real.norm_eq_abs, ENNReal.abs_toReal, ← div_mul_div_comm, add_mul (b := (1 : ℝ)), one_mul]
  conv => enter [1, _, 2, 1]; rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  conv => enter [1, _, 2, 2]; rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [← ENNReal.toReal_rpow, ENNReal.toReal_ofNat, Nat.ofNat_pos, Real.rpow_add,
    ENNReal.toReal_mul]
  conv => enter [1, _, 1]; rw [mul_div_cancel_left₀ _ (by positivity)]
  conv => enter [3, 1]; rw [← mul_one (_ ^ _)]
  apply Tendsto.const_mul
  conv => enter [1]; change (fun n ↦ _) / (fun n ↦ _)
  rw [← Asymptotics.isEquivalent_iff_tendsto_one]; swap
  · filter_upwards with _
    apply ne_of_gt
    refine lt_of_le_of_lt ?_ <| (add_lt_add_right (ENNReal.toReal_pos (by positivity) hC)) _
    positivity
  refine Asymptotics.IsEquivalent.add_add_of_nonneg
    (by intro _; positivity) (by intro _; positivity) ?_ .refl
  apply Asymptotics.IsEquivalent.mul .refl
  apply Asymptotics.IsEquivalent.rpow_of_nonneg (by intro _; positivity)
  have h (k : ℕ) : ∀ᶠ (n : ℕ) in atTop, 0 ≤ Real.logb 2 c.toReal + (n + k + 2) * d := by
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (- Real.logb 2 c.toReal / d)
    rw [eventually_atTop]
    use n₀
    replace hn₀ : -Real.logb 2 c.toReal < d * ↑n₀ := by field_simp at hn₀; exact hn₀
    intro n hn
    rw [← neg_le_iff_add_nonneg']
    grw [hn₀, hn]
    suffices 0 ≤ (k : ℝ) * d + 2 * d by grind
    positivity
  apply Asymptotics.IsEquivalent.congr_right; swap
  · filter_upwards [h 0] with n h_nonneg
    rw [← add_zero (n : ℝ), ← Nat.cast_zero, ENNReal.toReal_ofReal h_nonneg]
  apply Asymptotics.IsEquivalent.congr_left; swap
  · filter_upwards [h 1] with n h_nonneg
    rw [← Nat.cast_one, ENNReal.toReal_ofReal h_nonneg]
  apply Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    apply tendsto_atTop_add_const_left
    rw [tendsto_mul_const_atTop_of_pos hd_pos]
    repeat apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine (Asymptotics.IsEquivalent.const_add_of_norm_tendsto_atTop ?_ ?_).symm; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    rw [tendsto_mul_const_atTop_of_pos hd_pos]
    repeat apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine Asymptotics.IsEquivalent.mul ?_ .refl
  simp only [add_assoc]
  apply Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop; swap
  · apply Tendsto.comp tendsto_norm_atTop_atTop
    apply tendsto_atTop_add_const_right
    exact tendsto_natCast_atTop_iff.mpr tendsto_id
  refine (Asymptotics.IsEquivalent.add_const_of_norm_tendsto_atTop .refl ?_).symm
  exact Tendsto.comp tendsto_norm_atTop_atTop (tendsto_natCast_atTop_iff.mpr tendsto_id)
end PseudoEMetricSpace

end ProbabilityTheory


