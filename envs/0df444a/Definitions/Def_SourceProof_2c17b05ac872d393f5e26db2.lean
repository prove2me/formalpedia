-- Prove2me | Definitions.Def_SourceProof_2c17b05ac872d393f5e26db2
-- name    : SourceProof_2c17b05ac872d393f5e26db2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:34.298855+00:00
-- url     : https://prove2.me/theorems/3ebae922-3992-510f-82b6-d5965c89d320
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.tendstoUCP_leftRiemannSum_rightLimitProcess

import Definitions.Def_StochLean_Probability_Process_Partition_LeftSampling_F002
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_3b5fdce895cd814116c8eb4e
import Definitions.Def_SourceProof_3bfb9ef0d258afe6eedb13c5
import Definitions.Def_SourceProof_44c235d61a2cdcb446e715a4
import Definitions.Def_SourceProof_4aad6e35fadea08fff8ce9d0
import Definitions.Def_SourceProof_51d9d89e44d55b7a2162d89e
import Definitions.Def_SourceProof_53bca36d7403deaa0689f5ec
import Definitions.Def_SourceProof_53d90595c026ce14255ca40b
import Definitions.Def_SourceProof_790b2f2d9706f0b80ab186f4
import Definitions.Def_SourceProof_83e2df15639a4620c7f37049
import Definitions.Def_SourceProof_8ecf5e2e38faa4146bc97a61
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a2cb63993a652b5632791121
import Definitions.Def_SourceProof_b85e3ba7734054825c5da417
import Definitions.Def_SourceProof_d33983359663d20877640616
import Definitions.Def_SourceProof_f60f6796fd78b83be1f764d1
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The fixed-source-step jump-displacement argument in Protter II.21

Sample the right-limit process of a fixed full source simple integrand. Exact
ceiling-endpoint formulas and right continuity of the integrator give actual
compact-uniform path convergence. Its increment-only limit retains the source
initial correction; it does not assume convergence of the sampled integrands.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory.SimplePredictableRep

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} {π : ℕ → StoppingTimePartition F}

theorem _root_.Prove2MeSourceProof.h_2c17b05ac872d393f5e26db2 [IsFiniteMeasure P]
    (H : SimplePredictableRep F) (hπ : StoppingTimePartition.IsTendingToIdentity π P)
    (haX : Adapted F X) (hF : F.IsUsual P) (hrX : HasCadlagPaths X P) :
    TendstoUCP P (fun n ↦ (π n).leftRiemannSumProcess (rightLimitProcess H.toProcess) X) atTop
      (fun t ω ↦ H.integralProcess X t ω - H.initial ω * X 0 ω) := by
  have hrH : ProbabilityTheory.HasCagladPaths H.toProcess P := ae_of_all _ (_root_.Prove2MeSourceProof.h_83e2df15639a4620c7f37049 H)
  have haY := (_root_.Prove2MeSourceProof.h_f60f6796fd78b83be1f764d1 (_root_.Prove2MeSourceProof.h_51d9d89e44d55b7a2162d89e H)) hF hrH
  have hrY := (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c (_root_.Prove2MeSourceProof.h_53bca36d7403deaa0689f5ec hrH))
  have hcoef (n : ℕ) (i : Fin (π n).size) :
      Measurable[((π n).point i.castSucc).measurableSpace]
        (fun ω ↦ ProbabilityTheory.rightLimitProcess H.toProcess ((π n).point i.castSucc ω) ω) :=
    (_root_.Prove2MeSourceProof.h_4aad6e35fadea08fff8ce9d0 haY.stronglyAdapted) hF hrY
      ((π n).point i.castSucc).isStoppingTime
  apply _root_.Prove2MeSourceProof.h_53d90595c026ce14255ca40b
  · intro n T
    apply _root_.Prove2MeSourceProof.h_790b2f2d9706f0b80ab186f4
    · intro t
      exact ((_root_.Prove2MeSourceProof.h_b85e3ba7734054825c5da417 (π n)) (haY 0) (hcoef n) haX hF
        (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hrX) t).mono (F.le t) le_rfl
    · intro t
      exact (((_root_.Prove2MeSourceProof.h_d33983359663d20877640616 H) haX hF (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c hrX) t).sub
        ((H.measurable_initial.mul (haX 0)).mono (F.mono bot_le) le_rfl)).mono (F.le t) le_rfl
    · exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_3b5fdce895cd814116c8eb4e (π n)) (haY 0)
        (hcoef n) hrX))
    · have hc : ProbabilityTheory.HasCadlagPaths (fun (_ : ℝ≥0) ω ↦ H.initial ω * X 0 ω) P := by
        apply ae_of_all
        intro ω
        exact _root_.Prove2MeSourceProof.h_a2cb63993a652b5632791121
          (continuous_const : Continuous (fun _ : ℝ≥0 ↦ H.initial ω * X 0 ω))
      exact (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_44c235d61a2cdcb446e715a4 ((_root_.Prove2MeSourceProof.h_3bfb9ef0d258afe6eedb13c5 H) hrX)) hc))
  · filter_upwards [hπ, hrX] with ω hπω hXω T
    exact _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mpr
      ((_root_.Prove2MeSourceProof.h_8ecf5e2e38faa4146bc97a61 H) hπω.1 hπω.2 hXω.1 T)
end ProbabilityTheory.SimplePredictableRep


