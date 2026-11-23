-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_NatCardMatricesMulEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_SatakeParameters_NatCardMatricesMulEqZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:19.124291+00:00
-- url     : https://prove2.me/theorems/925f377e-fad3-43b4-b9a6-b99cd02d928c
-- title:
--   Nat Card Matrices Mul Eq Zero
-- statement:
--   Definitions and structural lemmas for Nat Card Matrices Mul Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/NatCardMatricesMulEqZero.lean

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
namespace GlobalTheory
def killersEquiv {k : Type} [Field k] {m n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    {w : Matrix (Fin m) (Fin n) k // w * A = 0} ≃ (Fin m → LinearMap.ker (Aᵀ).mulVecLin) where
  toFun w i := ⟨w.1 i, by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
    funext l
    have := congrFun (congrFun w.2 i) l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  invFun f := ⟨Matrix.of fun i => (f i).1, by
    ext i l
    have h := (f i).2
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at h
    have := congrFun h l
    simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using this⟩
  left_inv w := by ext i l; rfl
  right_inv f := by ext i l; rfl
end GlobalTheory


