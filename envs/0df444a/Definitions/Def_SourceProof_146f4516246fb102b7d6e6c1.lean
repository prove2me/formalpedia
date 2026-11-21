-- Prove2me | Definitions.Def_SourceProof_146f4516246fb102b7d6e6c1
-- name    : SourceProof_146f4516246fb102b7d6e6c1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:53:39.805069+00:00
-- url     : https://prove2.me/theorems/76c5fc9d-4a8f-4e61-b985-414223db850c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Poisson.integral_mul_charAt_sub_one
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CharacterCompensator_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality removes the compensated integrals from the character's increment

For a square-integrable weight orthogonal to every compensated integral over the horizon, the
pairing with the character's increment `χ_t − 1` reduces to the pairing with the compensator: the
two compensated halves of the jump chain rule integrate to zero against the weight.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Compensator


theorem _root_.Prove2MeSourceProof.h_146f4516246fb102b7d6e6c1 (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (htT : t ≤ T) :
    ∫ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1) ∂P
      = ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P := by
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  set GRe := LevyStochCalc.Poisson.charReIntegrand N hℱ w (LevyStochCalc.Poisson.measurableSet_truncFam hBm t) hA hAν
    (LevyStochCalc.Poisson.truncFam_subset hBsub t) with hGRe
  set GIm := LevyStochCalc.Poisson.charImIntegrand N hℱ w (LevyStochCalc.Poisson.measurableSet_truncFam hBm t) hA hAν
    (LevyStochCalc.Poisson.truncFam_subset hBsub t) with hGIm
  have hid := LevyStochCalc.Poisson.ae_charAt_sub_one_eq_integral N hℱ w hBm hA hAν hT hBsub htT
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have hrRe : Integrable (fun ω => r ω * GRe.integral N hℱ ω) P :=
    hr2.integrable_mul (GRe.memLp N hℱ)
  have hrIm : Integrable (fun ω => r ω * GIm.integral N hℱ ω) P :=
    hr2.integrable_mul (GIm.memLp N hℱ)
  have hrχ : Integrable (fun ω => (r ω : ℂ) * (LevyStochCalc.Poisson.charAt N w Bfam t ω - 1)) P := by
    have h := hr1.ofReal.bdd_mul (c := 2)
      ((LevyStochCalc.Poisson.measurable_charAt N w hBm t).sub measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => LevyStochCalc.Poisson.norm_charAt_sub_one_le N w Bfam t ω)
    exact h.congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have h1 : Integrable (fun ω => ((r ω * GRe.integral N hℱ ω : ℝ) : ℂ)) P := hrRe.ofReal
  have h2 : Integrable (fun ω => ((r ω * GIm.integral N hℱ ω : ℝ) : ℂ) * Complex.I) P :=
    hrIm.ofReal.mul_const _
  have h12 : Integrable (fun ω => ((r ω * GRe.integral N hℱ ω : ℝ) : ℂ)
      + ((r ω * GIm.integral N hℱ ω : ℝ) : ℂ) * Complex.I) P := h1.add h2
  have hrK : Integrable (fun ω => (r ω : ℂ) * LevyStochCalc.Poisson.charCompensator N w Bfam A T t ω) P := by
    have hdiff : Integrable (fun ω => (r ω : ℂ) * (LevyStochCalc.Poisson.charAt N w Bfam t ω - 1)
        - ((r ω * GRe.integral N hℱ ω : ℝ) : ℂ)
        - ((r ω * GIm.integral N hℱ ω : ℝ) : ℂ) * Complex.I) P := (hrχ.sub h1).sub h2
    refine hdiff.congr ?_
    filter_upwards [hid] with ω hω
    simp only [LevyStochCalc.Poisson.charCompensator]
    rw [hω]
    push_cast
    ring
  calc ∫ ω, (r ω : ℂ) * (LevyStochCalc.Poisson.charAt N w Bfam t ω - 1) ∂P
      = ∫ ω, (((r ω * GRe.integral N hℱ ω : ℝ) : ℂ)
          + ((r ω * GIm.integral N hℱ ω : ℝ) : ℂ) * Complex.I
          + (r ω : ℂ) * LevyStochCalc.Poisson.charCompensator N w Bfam A T t ω) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hid] with ω hω
        simp only [LevyStochCalc.Poisson.charCompensator]
        rw [hω]
        push_cast
        ring
    _ = ((∫ ω, r ω * GRe.integral N hℱ ω ∂P : ℝ) : ℂ)
          + ((∫ ω, r ω * GIm.integral N hℱ ω ∂P : ℝ) : ℂ) * Complex.I
          + ∫ ω, (r ω : ℂ) * LevyStochCalc.Poisson.charCompensator N w Bfam A T t ω ∂P := by
        have e1 : ∫ ω, ((r ω * GRe.integral N hℱ ω : ℝ) : ℂ) ∂P
            = ((∫ ω, r ω * GRe.integral N hℱ ω ∂P : ℝ) : ℂ) := integral_ofReal
        have e2 : ∫ ω, ((r ω * GIm.integral N hℱ ω : ℝ) : ℂ) ∂P
            = ((∫ ω, r ω * GIm.integral N hℱ ω ∂P : ℝ) : ℂ) := integral_ofReal
        rw [integral_add h12 hrK, integral_add h1 h2, integral_mul_const, e1, e2]
    _ = ∫ ω, (r ω : ℂ) * LevyStochCalc.Poisson.charCompensator N w Bfam A T t ω ∂P := by
        rw [hperp GRe, hperp GIm]
        push_cast
        ring
end Compensator

end LevyStochCalc.Poisson


