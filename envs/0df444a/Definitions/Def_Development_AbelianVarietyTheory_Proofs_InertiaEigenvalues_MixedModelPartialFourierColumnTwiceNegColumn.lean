-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:54:30.739683+00:00
-- url     : https://prove2.me/theorems/96d9f775-bf3c-4d77-83ab-9302fed67b40
-- title:
--   Mixed Model Partial Fourier Column Twice Neg Column
-- statement:
--   Definitions and structural lemmas for Mixed Model Partial Fourier Column Twice Neg Column, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR.PartialInv
def intLat (F : Type) [NormedField F] [IsUltrametricDist F] (r : ℕ) : AddSubgroup (Fin r → F) where
  carrier := Set.univ.pi fun _ => Metric.closedBall (0 : F) 1
  zero_mem' := by intro i _; simp
  add_mem' := by
    intro a b ha hb i _
    have h1 := ha i trivial
    have h2 := hb i trivial
    simp only [mem_closedBall_zero_iff] at h1 h2 ⊢
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)
  neg_mem' := by
    intro a ha i _
    have h1 := ha i trivial
    simpa using h1
end GlobalTheory.JR.PartialInv


