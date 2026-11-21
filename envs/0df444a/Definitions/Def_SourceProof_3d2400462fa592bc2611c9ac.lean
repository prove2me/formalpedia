-- Prove2me | Definitions.Def_SourceProof_3d2400462fa592bc2611c9ac
-- name    : SourceProof_3d2400462fa592bc2611c9ac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:30:57.173292+00:00
-- url     : https://prove2.me/theorems/99742a57-5f66-484e-a39b-83be3b9f30f3
-- title:
--   LevyStochCalc source module: SourceProof_3d2400462fa592bc2611c9ac
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.weighted_box_sq_eq` comes from the `LevyStochCalc.Poisson.CompensatedDensityBoxIsometry` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_3d2400462fa592bc2611c9ac
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) g) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal := by
  have hbox_meas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hbox_fin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    LevyStochCalc.Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAf
  have h_indep := _root_.Prove2MeSourceProof.h_01934a565743d93c74864a2d N ℱ hℱ ha hab hA hAf hg
  have h_indep_sq : ProbabilityTheory.IndepFun g
      (fun ω => (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
    h_indep.comp measurable_id (measurable_id.pow_const 2)
  rw [h_indep_sq.integral_fun_mul_eq_mul_integral
      ((hg.mono (ℱ.le' a)).measurable.aestronglyMeasurable)
      (((ENNReal.measurable_toReal.comp
        (N.measurable_eval hbox_meas)).sub_const _).pow_const 2).aestronglyMeasurable,
    _root_.Prove2MeSourceProof.h_b329aafcf3facb3fc4e13667 N hbox_meas hbox_fin]
end LevyStochCalc.Poisson.Compensated


