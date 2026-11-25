-- Prove2me | Definitions.Def_SourceProof_d33983359663d20877640616
-- name    : SourceProof_d33983359663d20877640616
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:05:04.766631+00:00
-- url     : https://prove2.me/theorems/51778c94-04f5-4f83-b0db-4592b000047e
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.adapted_integralProcess

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F000
import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_IntegralProcess_F001
import Definitions.Def_SourceProof_013463e4574b0455441609f2
import Definitions.Def_SourceProof_5caa95db89fdd596c2cde105
import Definitions.Def_SourceProof_669e70af113890cd7317fc66
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_f27f0406d0856e73dc290674
import Definitions.Def_SourceProof_faea1308e58b2b1b6deb90cf
import Definitions.Def_SourceProof_fc4a2bac5634cdbfe2b154e5

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

theorem _root_.Prove2MeSourceProof.h_d33983359663d20877640616 (H : SimplePredictableRep F) (hX : Adapted F X)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P) :
    Adapted F (H.integralProcess X) := by
  intro t
  have hm (τ : ProbabilityTheory.FiniteStoppingTime F) :
      Measurable[F t] (fun ω ↦ X (min (τ ω) t) ω) := by
    have hs := ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hX.stronglyAdapted) hF hr τ.isStoppingTime).adapted t
    change Measurable[F t] (stoppedProcess X τ.withTop t) at hs
    simpa only [(fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_faea1308e58b2b1b6deb90cf p2mMethodArg0 τ) X, min_comm] using hs
  have hterm (i : Fin H.partition.size) : Measurable[F t] (fun ω ↦ H.coefficient i ω *
      (X (min (H.partition.point i.succ ω) t) ω -
        X (min (H.partition.point i.castSucc ω) t) ω)) := by
    have hc := (_root_.Prove2MeSourceProof.h_013463e4574b0455441609f2 (H.partition.point i.castSucc))
      (H.measurable_coefficient i) t
    have heq : (fun ω ↦ H.coefficient i ω *
        (X (min (H.partition.point i.succ ω) t) ω -
          X (min (H.partition.point i.castSucc ω) t) ω)) =
        fun ω ↦ (if H.partition.point i.castSucc ω < t then H.coefficient i ω else 0) *
          (X (min (H.partition.point i.succ ω) t) ω -
            X (min (H.partition.point i.castSucc ω) t) ω) := by
      funext ω
      by_cases ht : H.partition.point i.castSucc ω < t
      · simp only [if_pos ht]
      · have ha := le_of_not_gt ht
        have hb : t ≤ H.partition.point i.succ ω :=
          ha.trans ((_root_.Prove2MeSourceProof.h_fc4a2bac5634cdbfe2b154e5 (H.partition.path ω)) i)
        simp only [if_neg ht, min_eq_right ha, min_eq_right hb, sub_self, mul_zero]
    rw [heq]
    exact hc.mul ((hm _).sub (hm _))
  have hi := (H.measurable_initial.mono (F.mono (show (0 : ℝ≥0) ≤ t from bot_le)) le_rfl).mul
    ((hX 0).mono (F.mono (show (0 : ℝ≥0) ≤ t from bot_le)) le_rfl)
  have hs := hi.add (Finset.measurable_fun_sum univ (fun i _ ↦ hterm i))
  change Measurable[F t] (fun ω ↦ H.integralProcess X t ω)
  simp only [_root_.Prove2MeSourceProof.h_5caa95db89fdd596c2cde105]
  exact hs
end SimplePredictableRep

namespace IsSimplePredictable

variable {H : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


