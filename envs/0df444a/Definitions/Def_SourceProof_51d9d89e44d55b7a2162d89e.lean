-- Prove2me | Definitions.Def_SourceProof_51d9d89e44d55b7a2162d89e
-- name    : SourceProof_51d9d89e44d55b7a2162d89e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T07:59:48.557846+00:00
-- url     : https://prove2.me/theorems/c9914eac-658e-4b95-acb7-1db22e0c0aa4
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.adapted

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F001
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_F002
import Definitions.Def_SourceProof_2de3ac64de8bd31f1d59bd9f
import Definitions.Def_SourceProof_9d2aae30149707576aa509f3
import Definitions.Def_SourceProof_a9c44e06617a4753cffd0417
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Predictable
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Source simple predictable processes really are adapted, caglad and predictable

Coefficient measurability is used at the original left stopping endpoint. Neither
bounded coefficients nor strict separation of endpoints is assumed.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep
theorem _root_.Prove2MeSourceProof.h_51d9d89e44d55b7a2162d89e (H : SimplePredictableRep F) : Adapted F H.toProcess := by
  intro t
  by_cases ht : t = 0
  · subst t
    have heq : H.toProcess 0 = H.initial := funext ((_root_.Prove2MeSourceProof.h_a9c44e06617a4753cffd0417 H))
    rw [heq]
    exact H.measurable_initial
  · change Measurable[F t] (fun ω ↦ if t = 0 then H.initial ω else _)
    simp only [if_neg ht]
    exact Finset.measurable_fun_sum _ (fun i _ ↦
      (_root_.Prove2MeSourceProof.h_9d2aae30149707576aa509f3 (H.partition.point i.castSucc))
        (H.partition.point i.succ) (H.measurable_coefficient i) t)
end SimplePredictableRep

end ProbabilityTheory


