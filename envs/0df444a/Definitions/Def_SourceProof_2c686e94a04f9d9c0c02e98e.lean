-- Prove2me | Definitions.Def_SourceProof_2c686e94a04f9d9c0c02e98e
-- name    : SourceProof_2c686e94a04f9d9c0c02e98e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:09:31.572478+00:00
-- url     : https://prove2.me/theorems/d3a41708-5286-44e8-93eb-e7f1be6af417
-- title:
--   LevyStochCalc source module: SourceProof_2c686e94a04f9d9c0c02e98e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.diagonal_increment_lint` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionExistence_F001

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


theorem _root_.Prove2MeSourceProof.h_2c686e94a04f9d9c0c02e98e
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) ξ) :
    ∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW_def
  have h_ξ_meas : Measurable ξ :=
    (h_adapt.mono (ℱ.le a)).measurable
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_indep_F_ΔW := hℱ.indep ha hab
  have h_ξ_comap_le : MeasurableSpace.comap ξ inferInstance ≤ ℱ a :=
    h_adapt.measurable.comap_le
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ a] u := h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2
      = (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0) = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (b - a) := by
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian ha hab]
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) :=
        ProbabilityTheory.memLp_id_gaussianReal (μ := 0) (v := (⟨b - a, by linarith⟩ : NNReal)) 2
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩]
        fun x : ℝ => x ^ 2 := by filter_upwards with x; positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int, mul_comm]
end LevyStochCalc.Brownian.Ito


