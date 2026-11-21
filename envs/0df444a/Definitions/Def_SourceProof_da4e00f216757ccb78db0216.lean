-- Prove2me | Definitions.Def_SourceProof_da4e00f216757ccb78db0216
-- name    : SourceProof_da4e00f216757ccb78db0216
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:44:40.49793+00:00
-- url     : https://prove2.me/theorems/8232a84f-51d3-4d79-9d0a-e8dbe625026c
-- title:
--   LevyStochCalc source module: SourceProof_da4e00f216757ccb78db0216
-- statement:
--   The original source theorem `LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_isEmpty` comes from the `LevyStochCalc.Driver.JointPRPDegenerate` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_JointPRPDegenerate_F000
import Definitions.Def_SourceProof_e552f76f67c7e2f43cdc6a09

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The degenerate cases of the joint representation

Without Brownian coordinates the joint filtration is the Poisson one and the representation is
the compensated integral alone; without marks the Poisson random measure carries no information
and the representation is the Brownian one alone. Splitting on the two cases removes the
implementation hypotheses `0 < d` and `Nonempty E` from the representation theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Trivial

end Trivial

section Degenerate

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in

theorem _root_.Prove2MeSourceProof.h_da4e00f216757ccb78db0216 [IsEmpty E] (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  have hfe : LevyStochCalc.Brownian.augFiltration D.filtration P T
      = LevyStochCalc.Probability.aug (D.W.naturalFiltration T) ‹MeasurableSpace Ω› P := by
    change LevyStochCalc.Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le, LevyStochCalc.Driver.LevyDriver.filtration_apply, LevyStochCalc.Driver.LevyDriver.naturalFiltration_poisson_eq_bot, sup_bot_eq]
  refine _root_.Prove2MeSourceProof.h_8f9f280f81d8e75768b9aa58 (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (LevyStochCalc.Driver.LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 hrB _
  obtain ⟨r₁, hr₁m, hrr₁⟩ := hrm
  rw [hfe] at hr₁m
  obtain ⟨Y, hYm, hY⟩ := LevyStochCalc.Probability.aestronglyMeasurable_of_stronglyMeasurable_aug hr₁m
  have hrY : r =ᵐ[P] Y := hrr₁.trans hY
  have hY2 : MemLp Y 2 P := hr2.ae_eq hrY
  have hY0 : ∫ ω, Y ω ∂P = 0 := by rw [← integral_congr_ae hrY]; exact hr0
  have hYmeas : Measurable Y := (hYm.mono (D.W.naturalFiltration.le T)).measurable
  have hYB : ∀ (i : Fin d) (G : LevyStochCalc.Brownian.Ito.HorizonIntegrand P (LevyStochCalc.Brownian.augFiltration D.filtration P) T),
      ∫ ω, Y ω * G.integral (D.W.W i) (D.isBrownianFiltration_aug i) ω ∂P = 0 := by
    intro i G
    rw [← hrB i G]
    refine integral_congr_ae ?_
    filter_upwards [hrY] with ω e
    simp only [e]
  have hYaug : AEStronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P T] Y P :=
    (hYm.mono ((D.naturalFiltration_brownian_le T).trans
      (LevyStochCalc.Brownian.le_augFiltration D.filtration P T))).aestronglyMeasurable
  have hYc2 : MemLp (fun ω => ((Y ω : ℝ) : ℂ)) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hY2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => Complex.norm_real (Y ω))]
    exact hY2.2
  have hYc0 : ∫ ω, ((Y ω : ℝ) : ℂ) ∂P = 0 := by
    rw [integral_complex_ofReal, hY0, Complex.ofReal_zero]
  have hperp : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.PerpItoIntegrals (D.W.W i) (LevyStochCalc.Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => ((Y ω : ℝ) : ℂ) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := _root_.Prove2MeSourceProof.h_e552f76f67c7e2f43cdc6a09 (D.W.W i)
      (D.isBrownianFiltration_aug i) hT hY2 hYaug (hYB i) K hm hp hq ht
    have hcast : (fun ω => ((Y ω : ℝ) : ℂ) * ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W i)
          (LevyStochCalc.Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((Y ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W i)
          (LevyStochCalc.Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  have hzero := LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals D.W (LevyStochCalc.Brownian.augFiltration D.filtration P)
    (fun k => D.isBrownianFiltration_aug k) (fun hc => D.isBrownianFiltration_combineBM_aug hc)
    (fun _ ht => D.augFiltration_le_of_nonpos ht)
    (fun _ hs h0 => D.measurableSet_augFiltration_of_null hs h0)
    (Complex.measurable_ofReal.comp hYmeas) hYc2 hperp hYc0
    (Complex.continuous_ofReal.comp_stronglyMeasurable hYm)
  refine hrY.trans ?_
  filter_upwards [hzero] with ω hω
  have hc : ((Y ω : ℝ) : ℂ) = 0 := hω
  exact_mod_cast hc
end Degenerate

end LevyDriver

end LevyStochCalc.Driver


