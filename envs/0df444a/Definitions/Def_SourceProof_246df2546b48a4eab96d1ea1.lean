-- Prove2me | Definitions.Def_SourceProof_246df2546b48a4eab96d1ea1
-- name    : SourceProof_246df2546b48a4eab96d1ea1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T17:08:36.939347+00:00
-- url     : https://prove2.me/theorems/4310ca74-0e30-4652-98a4-ceda72a9712a
-- title:
--   LevyStochCalc source module: SourceProof_246df2546b48a4eab96d1ea1
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero` comes from the `LevyStochCalc.Brownian.ItoL2CompletionIncrement` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_246df2546b48a4eab96d1ea1
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂) :
    ∫ ω, (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)) ∂P = 0 := by
  set ΔW₁ : Ω → ℝ := fun ω => W.W b₁ ω - W.W a₁ ω with hΔW₁_def
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  set f : Ω → ℝ := fun ω => ξ₁ ω * ΔW₁ ω * ξ₂ ω with hf_def
  have h_factored : (fun ω => (ξ₁ ω * ΔW₁ ω) * (ξ₂ ω * ΔW₂ ω)) = fun ω => f ω * ΔW₂ ω := by
    funext ω; simp only [hf_def]; ring
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => f ω * ΔW₂ ω from h_factored]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas)).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : MeasurableSet[ℱ a₂] u := h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v hu_F hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := by
    rw [show ∫ ω, ΔW₂ ω ∂P = ∫ x, x ∂(P.map ΔW₂) from
      (MeasureTheory.integral_map h_ΔW₂_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian ha₂_nn h₂]
    exact ProbabilityTheory.integral_id_gaussianReal
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl]
  rw [h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable]
  rw [h_ΔW₂_mean, mul_zero]
end LevyStochCalc.Brownian.Ito


