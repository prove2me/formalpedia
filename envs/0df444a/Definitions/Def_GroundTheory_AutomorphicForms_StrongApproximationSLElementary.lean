-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- name    : GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:12:10.784836+00:00
-- url     : https://prove2.me/theorems/0305ea35-6b8e-4da1-9847-aaeb2a6c284c
-- title:
--   Strong Approximation SLElementary
-- statement:
--   Definitions and structural lemmas for Strong Approximation SLElementary, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean

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
namespace GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
section CommRing
variable (n) (R : Type*) [CommRing R]
def transvectionGL (t : TransvectionStruct n R) : GL n R where
  val := t.toMatrix
  inv := t.inv.toMatrix
  val_inv := TransvectionStruct.mul_inv t
  inv_val := TransvectionStruct.inv_mul t
@[simp]
theorem coe_transvectionGL (t : TransvectionStruct n R) :
    (transvectionGL n R t : Matrix n n R) = t.toMatrix := rfl
def elementarySubgroup : Subgroup (GL n R) :=
  Subgroup.closure (Set.range (transvectionGL n R))
variable {n R}
def diagonalGL : (n → Rˣ) →* GL n R where
  toFun d :=
    { val := diagonal fun k => (d k : R)
      inv := diagonal fun k => (↑(d k)⁻¹ : R)
      val_inv := by simp [diagonal_mul_diagonal]
      inv_val := by simp [diagonal_mul_diagonal] }
  map_one' := by ext1; simp
  map_mul' d e := by ext1; simp [diagonal_mul_diagonal]
end CommRing
section Field
variable {F : Type*} [Field F]
end Field
end GroundTheory.Automorphic


