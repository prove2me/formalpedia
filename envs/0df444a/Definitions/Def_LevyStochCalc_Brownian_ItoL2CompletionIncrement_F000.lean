-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionIncrement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:10:42.879574+00:00
-- url     : https://prove2.me/theorems/15093fe6-43a8-4a5d-9906-d6834d47ff84
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionIncrement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionIncrement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001
import Definitions.Def_SourceProof_2c686e94a04f9d9c0c02e98e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: increment expansions and the intermediate-time isometry

Diagonal and off-diagonal expectations of products of Brownian increments against
adapted weights, the Bochner expansion of the square of a simple integral clamped
at an intermediate time, and the isometry
`∫⁻ ‖simpleIntegral W H t‖₊² = ∫⁻ ∫⁻_{[0, t]} ‖H.eval‖₊²` it gives for every
intermediate time `t`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Square-integrability of a Brownian increment** over `[s,t]` (general `s<t`).
A non-`private` companion of `ItoSimple`'s helper, needed below. -/
lemma increment_sq_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω) ^ 2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  rw [show (fun ω => (W.W t ω - W.W s ω) ^ 2)
        = (fun x : ℝ => x ^ 2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => W.W t ω - W.W s ω)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (P.map (fun ω => W.W t ω - W.W s ω))) h_meas.aemeasurable).symm]
  rw [W.increment_gaussian hs hst]
  have h := (ProbabilityTheory.memLp_id_gaussianReal
    (μ := 0) (v := (⟨t - s, by linarith⟩ : NNReal)) 2).integrable_norm_pow
    (p := 2) (by norm_num)
  convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]
/-- **General two-time diagonal, Bochner form.** `∫ (ξ·(W_b−W_a))² = (b−a)·∫ ξ²`
for `0 ≤ a < b`, `ξ` `F_a`-measurable and bounded (`|ξ| ≤ M`). Bochner companion
of `diagonal_increment_lint`, for the Bochner sum-expansion in the isometry. -/
lemma diagonal_increment_bochner
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) ξ)
    (M : ℝ) (h_bound : ∀ ω, |ξ ω| ≤ M) :
    ∫ ω, (ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P = (b - a) * ∫ ω, (ξ ω) ^ 2 ∂P := by
  have hξ_meas : Measurable ξ :=
    (h_adapt.mono (ℱ.le a)).measurable
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := _root_.Prove2MeSourceProof.h_2c686e94a04f9d9c0c02e98e W ℱ hℱ ha hab ξ h_adapt
  rw [show (∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((ξ ω * (W.W b ω - W.W a ω)) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P) = ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  have h_xi_sq_bound : ∀ ω, (ξ ω) ^ 2 ≤ M ^ 2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (h_bound ω)) (le_of_abs_le (h_bound ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (ξ ω) ^ 2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_int_ΔW_sq := increment_sq_integrable W ha hab
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2) P := by
    rw [show (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2)
            = fun ω => (ξ ω) ^ 2 * (W.W b ω - W.W a ω) ^ 2 from by funext ω; ring]
    refine MeasureTheory.Integrable.bdd_mul (c := M ^ 2) h_int_ΔW_sq
      (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (ξ ω) ^ 2 := by filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  have h_dt_nn : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  rw [show ENNReal.ofReal (b - a) * ENNReal.ofReal (∫ ω, (ξ ω) ^ 2 ∂P)
          = ENNReal.ofReal ((b - a) * ∫ ω, (ξ ω) ^ 2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  exact (ENNReal.ofReal_eq_ofReal_iff
    (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    (mul_nonneg h_dt_nn (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))).mp h_lint
end LevyStochCalc.Brownian.Ito


