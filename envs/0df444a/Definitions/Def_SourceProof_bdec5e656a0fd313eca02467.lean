-- Prove2me | Definitions.Def_SourceProof_bdec5e656a0fd313eca02467
-- name    : SourceProof_bdec5e656a0fd313eca02467
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:33:40.054187+00:00
-- url     : https://prove2.me/theorems/696a5b49-f9de-5b6a-8016-97ba29dc73cf
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.hasMonotonePaths_quadraticVariation_of_partition

import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Definitions.Def_StochLean_Probability_Process_Partition_SquareSums_F000
import Definitions.Def_SourceProof_34709e9a71549d163a00e849
import Definitions.Def_SourceProof_51c0da11e7e46e13ea7b46dd
import Definitions.Def_SourceProof_52204861332fb91251d9b5c4
import Definitions.Def_SourceProof_9183846313e90de3d6561ee0
import Definitions.Def_SourceProof_944fa57bc3b71053cbab118a
import Definitions.Def_SourceProof_b0ba1bc04ac80bc678071fe6
import Definitions.Def_SourceProof_c3a38a53524388b4ac4c79ee
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.UniformSpace.UniformApproximation

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Increasing paths of the canonical raw quadratic variation

The partial-cell square sums are not assumed monotone. Evaluating each sum
at the next partition endpoint produces monotone completed-cell sums. A
locally uniform subsequence and right continuity identify their pointwise
limit with the raw bracket on one event for all times together.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_bdec5e656a0fd313eca02467
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    {π : ℕ → StoppingTimePartition F} (hπ : StoppingTimePartition.IsTendingToIdentity π P) :
    HasMonotonePaths (hX.quadraticVariation hF) P := by
  obtain ⟨k, hk, hU⟩ :=
    (_root_.Prove2MeSourceProof.h_944fa57bc3b71053cbab118a ((_root_.Prove2MeSourceProof.h_c3a38a53524388b4ac4c79ee hX) hF hπ))
  filter_upwards [hπ, hU, (_root_.Prove2MeSourceProof.h_51c0da11e7e46e13ea7b46dd hX) hF] with ω hπω hu hQ
  have hT : Tendsto (fun n ↦ (π (k n)).terminal ω) atTop atTop := hπω.1.comp hk.tendsto_atTop
  have hm : Tendsto (fun n ↦ ((π (k n)).mesh ω : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp (hπω.2.comp hk.tendsto_atTop)
  have heval (s : ℝ≥0) : Tendsto (fun n ↦ (π (k n)).quadraticVariationSumProcess X
      (((π (k n)).path ω).ceilingPoint s) ω) atTop (𝓝 (hX.quadraticVariation hF s ω)) := by
    apply _root_.Prove2MeSourceProof.h_b0ba1bc04ac80bc678071fe6
      (fun T ↦ _root_.Prove2MeSourceProof.h_9183846313e90de3d6561ee0.mp (hu T)) hQ.1
    exact _root_.Prove2MeSourceProof.h_34709e9a71549d163a00e849
      (fun n ↦ (π (k n)).path ω) s (hT.eventually (eventually_ge_atTop s)) hm
  intro s t hst
  apply le_of_tendsto_of_tendsto (heval s) (heval t)
  apply Eventually.of_forall
  intro n
  exact add_le_add le_rfl (_root_.Prove2MeSourceProof.h_52204861332fb91251d9b5c4
    ((π (k n)).path ω) (X · ω) hst)
end IsSemimartingale

end ProbabilityTheory


