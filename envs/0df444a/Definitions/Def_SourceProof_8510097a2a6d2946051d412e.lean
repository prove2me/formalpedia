-- Prove2me | Definitions.Def_SourceProof_8510097a2a6d2946051d412e
-- name    : SourceProof_8510097a2a6d2946051d412e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:56:48.568394+00:00
-- url     : https://prove2.me/theorems/2ece9414-37e6-4389-84be-fe2b5fb1e068
-- title:
--   StochLean source theorem: StochLean.measurable_stieltjesContinuousPart_of_measurable_upTo

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesContinuousPart_F000
import Definitions.Def_SourceProof_561d7fc50af0bdd1f0a29ad5
import Definitions.Def_SourceProof_ca1768529b4cdee6d56d9537
import Definitions.Def_SourceProof_cea06ce35b1a746f3e8af6f7
import Definitions.Def_SourceProof_d7eb2c626d75e3179e5022d6

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component is measurable from the path up to that time

Only the finite restriction through the requested time is used. This is the
nonanticipation bridge needed for adapted continuous quadratic variation.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_8510097a2a6d2946051d412e
    {Ω : Type*} [MeasurableSpace Ω] {B : Ω → StieltjesFunction ℝ≥0} (T : ℝ≥0)
    (hB : ∀ t ≤ T, Measurable fun ω ↦ B ω t) :
    Measurable fun ω ↦ stieltjesContinuousPart (B ω) T := by
  let κ : Kernel Ω ℝ≥0 := ⟨fun ω ↦ (B ω).measure.restrict (Iic T),
    _root_.Prove2MeSourceProof.h_cea06ce35b1a746f3e8af6f7 T hB⟩
  have hκ (ω : Ω) : IsFiniteMeasure (κ ω) := by
    refine ⟨?_⟩
    change ((B ω).measure.restrict (Iic T)) univ < ∞
    rw [Measure.restrict_apply_univ, _root_.Prove2MeSourceProof.h_561d7fc50af0bdd1f0a29ad5]
    exact ENNReal.ofReal_lt_top
  have h := ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe MeasurableSet.univ).comp
      (_root_.Prove2MeSourceProof.h_ca1768529b4cdee6d56d9537 κ hκ))
  have heq (ω : Ω) : ((StochLean.pointDiffusePart (κ ω)) univ).toReal =
      StochLean.stieltjesContinuousPart (B ω) T := by
    change (StochLean.pointDiffusePart ((B ω).measure.restrict (Iic T))).real univ = _
    rw [_root_.Prove2MeSourceProof.h_d7eb2c626d75e3179e5022d6 _ measurableSet_Iic, measureReal_restrict_apply_univ]
    rfl
  simpa only [Function.comp_def, heq] using h
end StochLean


