-- Prove2me | Definitions.Def_SourceProof_65e5da2938d5b7e0eab633e9
-- name    : SourceProof_65e5da2938d5b7e0eab633e9
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:05:46.410802+00:00
-- url     : https://prove2.me/theorems/c4b44ee2-3fec-4b85-8dfe-32e3f32fe2aa
-- title:
--   LevyStochCalc source module: SourceProof_65e5da2938d5b7e0eab633e9
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.offDiagonal_increment_integral_zero_weighted` comes from the `LevyStochCalc.Brownian.ItoL2CompletionCompensator` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the compensated square of a simple integral

Weighted off-diagonal vanishing for products of Brownian increments, the clamped
expansion of the square of a difference of simple integrals, and the martingale
property of the compensated square
`(simpleIntegral W H t)² − ∫_{[0, t]} (H.eval u)² du` with respect to the
filtration `ℱ`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_65e5da2938d5b7e0eab633e9
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono (ℱ.le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono (ℱ.le a₂)).measurable
  have hgmeas : Measurable g :=
    (hg.mono (ℱ.le a₁)).measurable
  set f : Ω → ℝ := fun ω => g ω * (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * ξ₂ ω with hf_def
  rw [show (fun ω => g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * ΔW₂ ω)))
        = fun ω => f ω * ΔW₂ ω from by funext ω; simp only [hf_def]; ring]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W b₁) :=
    ((hℱ.measurable b₁).stronglyMeasurable).mono
      (ℱ.mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) (W.W a₁) :=
    ((hℱ.measurable a₁).stronglyMeasurable).mono
      (ℱ.mono
        (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) ξ₁ :=
    hadapt₁.mono (ℱ.mono ha₁a₂)
  have h_g_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) g :=
    hg.mono (ℱ.mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a₂) f :=
    (h_g_F_meas.mul (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas))).mul hadapt₂
  have h_indep_F_ΔW₂ := hℱ.indep ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hgmeas.mul (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁)))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le : MeasurableSpace.comap f inferInstance ≤ ℱ a₂ :=
    h_f_F_meas.measurable.comap_le
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v (h_f_comap_le u hu) hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := LevyStochCalc.Brownian.Ito.brownian_incr_mean W ha₂_nn h₂
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl,
    h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable, h_ΔW₂_mean, mul_zero]
end LevyStochCalc.Brownian.Ito


