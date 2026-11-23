-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsInducedIntPrimeTo
-- name    : Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsInducedIntPrimeTo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:41.930953+00:00
-- url     : https://prove2.me/theorems/a5d3cc4c-2205-46d0-88fb-a5d7cf87187c
-- title:
--   Exists Induced Int Prime To
-- statement:
--   Definitions and structural lemmas for Exists Induced Int Prime To, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExistsInducedIntPrimeTo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.ElemLocal
def cycMul {G : Type} [Group G] (c : G) (P : Subgroup G) (h : ∀ y ∈ P, Commute c y) :
    Subgroup G where
  carrier := {g | ∃ i : ℤ, ∃ y ∈ P, g = c ^ i * y}
  one_mem' := ⟨0, 1, P.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨i, y, hy, rfl⟩ ⟨j, z, hz, rfl⟩
    refine ⟨i + j, y * z, P.mul_mem hy hz, ?_⟩
    have := ((h y hy).zpow_left j).eq
    rw [zpow_add, mul_assoc, ← mul_assoc y, ← this]
    simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨i, y, hy, rfl⟩
    refine ⟨-i, y⁻¹, P.inv_mem hy, ?_⟩
    have := ((h _ (P.inv_mem hy)).zpow_left (-i)).eq
    rw [this, mul_inv_rev, zpow_neg]
end GlobalTheory.ElemLocal


