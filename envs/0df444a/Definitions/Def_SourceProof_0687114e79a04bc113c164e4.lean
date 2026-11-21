-- Prove2me | Definitions.Def_SourceProof_0687114e79a04bc113c164e4
-- name    : SourceProof_0687114e79a04bc113c164e4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:30:26.829054+00:00
-- url     : https://prove2.me/theorems/3c49c3b6-f1bc-4114-882f-2e0d11364427
-- title:
--   LevyStochCalc source module: SourceProof_0687114e79a04bc113c164e4
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_cross_timeordered_zero` comes from the `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityStepIntegral_F002
import Definitions.Def_SourceProof_01934a565743d93c74864a2d

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Weighted covariances of compensated boxes

Second moments and cross moments of compensated masses `Ñ((a,b] × A)` weighted by a
past-measurable factor: the weighted second moment, vanishing of the cross terms for disjoint
marks and for time-ordered boxes, and the same-time bilinear covariance in the marks. These
combine into the isometry for a single time interval carrying several marks.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_0687114e79a04bc113c164e4
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b c d : ℝ} (hc : 0 ≤ c) (hbc : b ≤ c) (hcd : c < d)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A') (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ c) g) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω) ∂P = 0 := by
  have hRmeas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet (Set.Ioc c d ×ˢ A') := measurableSet_Ioc.prod hA'
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ A') ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hA'f
  have hRsub : Set.Ioc a b ×ˢ A ⊆ Set.Iic c ×ˢ Set.univ :=
    fun x hx => ⟨le_trans hx.1.2 hbc, Set.mem_univ _⟩
  -- `Ñ((a,b]×A)` is past-at-`c` measurable.
  have hÑR_c : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact (((hℱ.measurable hRsub
      hRmeas).ennreal_toReal).sub measurable_const).stronglyMeasurable
  have hf_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω) :=
    hg.mul hÑR_c
  have h_indep : ProbabilityTheory.IndepFun
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
      (fun ω => N.compensated (Set.Ioc c d ×ˢ A') ω) P :=
    _root_.Prove2MeSourceProof.h_01934a565743d93c74864a2d N ℱ hℱ hc hcd hA' hA'f hf_meas
  rw [show (fun ω => g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω))
      = (fun ω => (g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
          * N.compensated (Set.Ioc c d ×ˢ A') ω) from by funext ω; ring,
    h_indep.integral_fun_mul_eq_mul_integral
      (hf_meas.mono (ℱ.le' c)).measurable.aestronglyMeasurable
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval hR'meas)).sub_const _).aestronglyMeasurable,
    _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed N hR'meas hR'f, mul_zero]
end LevyStochCalc.Poisson.Compensated


