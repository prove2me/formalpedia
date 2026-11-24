-- Prove2me | Definitions.Def_SourceProof_1b5811523ebf232c3a8b514f
-- name    : SourceProof_1b5811523ebf232c3a8b514f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T21:46:32.821014+00:00
-- url     : https://prove2.me/theorems/9835db4d-bab7-4ff2-a705-0f6e3eaa2571
-- title:
--   StochLean source theorem: ProbabilityTheory.IsModification.indistinguishable_of_rightContinuous

import Definitions.Def_StochLean_Probability_Process_Path_RightContinuous_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Almost-sure right-continuous paths
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace ProbabilityTheory

section PathDefinitions

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [Preorder T] [TopologicalSpace T] [TopologicalSpace E]

namespace HasRightContinuousPaths

variable {X Y : T → Ω → E} {P : Measure Ω}

end HasRightContinuousPaths

end PathDefinitions

namespace IsModification

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder T] [TopologicalSpace T] [OrderTopology T] [DenselyOrdered T] [NoMaxOrder T]
  [FirstCountableTopology T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
  [TopologicalSpace E] [T2Space E] {X Y : T → Ω → E} {P : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_1b5811523ebf232c3a8b514f
    (hmod : IsModification X Y P)
    (hX : HasRightContinuousPaths X P)
    (hY : HasRightContinuousPaths Y P) :
    Indistinguishable X Y P := by
  have hdense : ∀ᵐ ω ∂P, ∀ n, X (TopologicalSpace.denseSeq T n) ω =
      Y (TopologicalSpace.denseSeq T n) ω := by
    rw [ae_all_iff]
    exact fun n ↦ hmod (TopologicalSpace.denseSeq T n)
  filter_upwards [hdense, hX, hY] with ω hω hXω hYω
  intro t
  have hD : Dense (Set.range (TopologicalSpace.denseSeq T)) :=
    TopologicalSpace.denseRange_denseSeq T
  obtain ⟨u, _huanti, hu, hlim⟩ := hD.exists_seq_strictAnti_tendsto t
  have hwithin : Tendsto u atTop (nhdsWithin t (Ici t)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlim, Eventually.of_forall fun n ↦ Set.mem_Ici.mpr (hu n).1.le⟩
  have hXt : Tendsto (fun n ↦ X (u n) ω) atTop (𝓝 (X t ω)) :=
    (hXω t).tendsto.comp hwithin
  have hYt : Tendsto (fun n ↦ Y (u n) ω) atTop (𝓝 (Y t ω)) :=
    (hYω t).tendsto.comp hwithin
  have hseq : ∀ n, X (u n) ω = Y (u n) ω := by
    intro n
    obtain ⟨k, hk⟩ := (hu n).2
    rw [← hk]
    exact hω k
  exact tendsto_nhds_unique hXt
    (hYt.congr' (Eventually.of_forall fun n ↦ (hseq n).symm))
end IsModification

end ProbabilityTheory


