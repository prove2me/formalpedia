-- Prove2me | Definitions.Def_SourceProof_8d1ecfa3e3f6d8e45cbcc4bf
-- name    : SourceProof_8d1ecfa3e3f6d8e45cbcc4bf
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:31:20.089056+00:00
-- url     : https://prove2.me/theorems/a557aefe-945e-5e5a-a8ed-feacd539a8a6
-- title:
--   StochLean source theorem: MeasureTheory.isUIMartingale_indicator_stoppingTime_le_of_condExp_before_eq_zero

import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F000
import Definitions.Def_StochLean_Probability_Process_LocalMartingale_F001
import Definitions.Def_StochLean_Probability_Process_Stopping_BeforeSigma_F000
import Definitions.Def_SourceProof_03e63d7ecbdfc90f21e5b93e
import Definitions.Def_SourceProof_39f3270bf0bf534c8acd6bca
import Definitions.Def_SourceProof_7697f46ddf08897a14ff00d9
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Before-centered integrable single jumps are UI martingales

The coefficient is measurable at the stopping time, not necessarily before it.
If its conditional expectation before that time vanishes, its actual closed
lifetime step is a martingale. Integrable domination of all stopping values
gives Class D and hence uniform integrability.

No predictability of the lifetime is needed for this centered martingale
statement. Predictability is needed separately to identify the removed
before-conditional step as a predictable compensating process. Infinite
lifetimes never activate at finite time; coefficients are not assumed zero
there and no finite evaluation of an infinite stopping time is used.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} {Z : Ω → ℝ}


theorem _root_.Prove2MeSourceProof.h_8d1ecfa3e3f6d8e45cbcc4bf
    (hτ : IsStoppingTime F τ) (hm : StronglyMeasurable[hτ.measurableSpace] Z)
    (hi : Integrable Z P) (hz : P[Z | hτ.measurableSpaceBefore] =ᵐ[P] 0) :
    IsUIMartingale (fun t : ℝ≥0 ↦ {ω | τ ω ≤ (t : WithTop ℝ≥0)}.indicator Z) F P :=
  ⟨_root_.Prove2MeSourceProof.h_39f3270bf0bf534c8acd6bca hτ hm hi hz,
    (_root_.Prove2MeSourceProof.h_03e63d7ecbdfc90f21e5b93e (_root_.Prove2MeSourceProof.h_7697f46ddf08897a14ff00d9 hτ hm hi))⟩
end MeasureTheory


