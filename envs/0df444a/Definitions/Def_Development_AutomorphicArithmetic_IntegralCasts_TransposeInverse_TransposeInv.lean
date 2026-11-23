-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
-- name    : Development_AutomorphicArithmetic_IntegralCasts_TransposeInverse_TransposeInv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:23.227985+00:00
-- url     : https://prove2.me/theorems/e880884b-c728-4797-8c5d-e7777a9d8280
-- title:
--   Transpose Inv
-- statement:
--   Definitions and structural lemmas for Transpose Inv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/TransposeInverse/TransposeInv.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Reformulated.TransposeInverseTheory
open Matrix
variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
def transposeInvFun (g : GL n R) : GL n R where
  val := ((g⁻¹ : GL n R) : Matrix n n R)ᵀ
  inv := (g : Matrix n n R)ᵀ
  val_inv := by rw [← transpose_mul, Units.mul_inv, transpose_one]
  inv_val := by rw [← transpose_mul, Units.inv_mul, transpose_one]
theorem transposeInvFun_involutive :
    Function.Involutive (transposeInvFun : GL n R → GL n R) := by
  intro g
  apply Units.ext
  exact transpose_transpose _
def transposeInv : GL n R ≃* GL n R where
  toFun := transposeInvFun
  invFun := transposeInvFun
  left_inv := transposeInvFun_involutive
  right_inv := transposeInvFun_involutive
  map_mul' g h := by
    apply Units.ext
    change (((g * h)⁻¹ : GL n R) : Matrix n n R)ᵀ =
      ((g⁻¹ : GL n R) : Matrix n n R)ᵀ * ((h⁻¹ : GL n R) : Matrix n n R)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul]
end Reformulated.TransposeInverseTheory


