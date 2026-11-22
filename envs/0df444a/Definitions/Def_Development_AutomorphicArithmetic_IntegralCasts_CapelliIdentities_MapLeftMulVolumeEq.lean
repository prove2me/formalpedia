-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MapLeftMulVolumeEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:52:33.440648+00:00
-- url     : https://prove2.me/theorems/ab5d2bbf-e484-4517-886f-670378599207
-- title:
--   Map Left Mul Volume Eq
-- statement:
--   Definitions and structural lemmas for Map Left Mul Volume Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MapLeftMulVolumeEq.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
def UpperTheory.matrixSpaceLinearEquiv (n : ℕ) : (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun x := fun i j => x j i
  invFun x := fun i j => x j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
noncomputable def UpperTheory.matrixLeftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  (UpperTheory.matrixSpaceLinearEquiv n).toLinearMap ∘ₗ
    (LinearMap.pi fun j : Fin n => (Matrix.toLin' (Matrix.of a)).comp (LinearMap.proj j)) ∘ₗ
    (UpperTheory.matrixSpaceLinearEquiv n).symm.toLinearMap


