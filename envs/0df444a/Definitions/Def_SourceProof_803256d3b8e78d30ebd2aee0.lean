-- Prove2me | Definitions.Def_SourceProof_803256d3b8e78d30ebd2aee0
-- name    : SourceProof_803256d3b8e78d30ebd2aee0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:14:36.963739+00:00
-- url     : https://prove2.me/theorems/54074011-4d1c-589f-952b-d0c07211cdf2
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.isCadlagPath_integralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_056f0ffa0965e1b3a522e2ff
import Definitions.Def_SourceProof_203c8143f8646ca99211fe57
import Definitions.Def_SourceProof_264b430747bbe6ee020dbafc
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_60b56e0d38c6166660de298f
import Definitions.Def_SourceProof_669e70af113890cd7317fc66
import Definitions.Def_SourceProof_7fe27d80761f531095784a17
import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Definitions.Def_SourceProof_d80df7975aaa241a180afe6d
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.LocalProperty

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Adaptedness and cadlag paths of the source elementary integral process

The coefficient is revealed only strictly after its left endpoint; before that endpoint
the stopped increment vanishes. Thus no anticipative coefficient measurability is assumed.
Path regularity is pathwise and needs no coefficient bound or integrability hypothesis.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_803256d3b8e78d30ebd2aee0 (H : SimplePredictableRep F) {ω : Ω}
    (hX : IsCadlagPath (X · ω)) : IsCadlagPath (H.integralProcess X · ω) := by
  have hsum := _root_.Prove2MeSourceProof.h_203c8143f8646ca99211fe57 Finset.univ
    (fun i : Fin H.partition.size ↦ fun t : ℝ≥0 ↦ H.coefficient i ω *
      (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω)) (fun i _ ↦ by
      have hb := (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff hX) (H.partition.point i.succ ω)
      have ha := (_root_.Prove2MeSourceProof.h_056f0ffa0965e1b3a522e2ff hX) (H.partition.point i.castSucc ω)
      have hd := (_root_.Prove2MeSourceProof.h_d80df7975aaa241a180afe6d hb) ((_root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f ha) continuous_neg)
      have hm := (_root_.Prove2MeSourceProof.h_60b56e0d38c6166660de298f (f := fun a : ℝ ↦ H.coefficient i ω * a) hd) (continuous_const.mul continuous_id)
      change ProbabilityTheory.IsCadlagPath (fun t ↦ H.coefficient i ω *
        (X (min t (H.partition.point i.succ ω)) ω +
          -X (min t (H.partition.point i.castSucc ω)) ω)) at hm
      simpa only [sub_eq_add_neg, min_comm] using hm)
  have hc : ProbabilityTheory.IsCadlagPath (fun _ : ℝ≥0 ↦ H.initial ω * X 0 ω) :=
    _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121 continuous_const
  simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105]
  exact (_root_.Prove2MeSourceProof.h_d80df7975aaa241a180afe6d hc) hsum
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


