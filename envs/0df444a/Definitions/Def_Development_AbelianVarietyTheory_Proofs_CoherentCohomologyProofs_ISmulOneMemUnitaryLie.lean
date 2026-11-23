-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ISmulOneMemUnitaryLie
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ISmulOneMemUnitaryLie
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:35.797548+00:00
-- url     : https://prove2.me/theorems/46849617-d7a9-47d0-b07d-c920bfd55f33
-- title:
--   ISmul One Mem Unitary Lie
-- statement:
--   Definitions and structural lemmas for ISmul One Mem Unitary Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ISmulOneMemUnitaryLie.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
namespace GlobalTheory.UnitaryLieAlgebra
variable {n : Type*} [Fintype n]
def unitaryLie (J : Matrix n n ℂ) : Submodule ℝ (Matrix n n ℂ) where
  carrier := {X | Xᴴ * J + J * X = 0}
  zero_mem' := by simp
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at hX hY ⊢
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  smul_mem' := by
    intro r X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX,
      smul_zero]
end GlobalTheory.UnitaryLieAlgebra


