-- Prove2me | Definitions.Def_SourceProof_1b57c1116b3f8ea72ca9d7fe
-- name    : SourceProof_1b57c1116b3f8ea72ca9d7fe
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:58:03.02645+00:00
-- url     : https://prove2.me/theorems/ceb3dfb9-549e-4cfc-b391-48f3eecb564e
-- title:
--   LevyStochCalc source module: SourceProof_1b57c1116b3f8ea72ca9d7fe
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.compensated_condExp_future_eq_zero` comes from the `LevyStochCalc.Poisson.CompensatedMartingaleAdapted` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F001
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometryL2_F002
import Definitions.Def_LevyStochCalc_Poisson_CompensatedIsometry_F001
import Definitions.Def_SourceProof_bed7648bbf21e6d2454c31ed
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Adapted

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to a Poisson filtration `ℱ` of `N`: each time-rectangle
`timeRect i t` lies in the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable,
and the coefficient `ξᵢ` is `ℱ_t`-measurable once `t` reaches the partition point (the term
vanishing before). Each summand is `P`-integrable, its conditional expectation satisfies
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` for `0 ≤ s ≤ t`, and summing over the
partition gives the martingale property of `t ↦ simpleIntegral N φ t`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_1b57c1116b3f8ea72ca9d7fe
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {s t' : ℝ} (hs : 0 ≤ s) (hst : s < t') {A : Set E} (hA : MeasurableSet A)
    (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc s t' ×ˢ A) ω
        | ℱ s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  set B : Set (ℝ × E) := Set.Ioc s t' ×ˢ A with hB
  have hB_meas : MeasurableSet B := measurableSet_Ioc.prod hA
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ := by
    rw [hB, LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ hA_fin
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hle₁ := (N.measurable_eval hB_meas).comap_le
  have hle₂ := ℱ.le' s
  have hg : @Measurable Ω ℝ≥0∞ (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _
      (fun ω => N.N ω B) := fun u hu => ⟨u, hu, rfl⟩
  have hf : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (fun ω => N.compensated B ω) :=
    ((hg.ennreal_toReal).sub_const _).stronglyMeasurable
  have hindep : ProbabilityTheory.Indep (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      (ℱ s) P := by
    exact (hℱ.indep hs hst hA hA_fin).symm
  refine (MeasureTheory.condExp_indep_eq hle₁ hle₂ hf hindep).trans ?_
  filter_upwards with ω
  exact _root_.Prove2MeSourceProof.h_bed7648bbf21e6d2454c31ed N hB_meas h_finite
end LevyStochCalc.Poisson.Compensated


