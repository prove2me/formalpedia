-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ConjTransposeBoostMulSignatureMulBoost
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:22.592135+00:00
-- url     : https://prove2.me/theorems/0f655124-bf3e-4e21-b9e0-b3a3fccb9e5a
-- title:
--   Conj Transpose Boost Mul Signature Mul Boost
-- statement:
--   Definitions and structural lemmas for Conj Transpose Boost Mul Signature Mul Boost, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ConjTransposeBoostMulSignatureMulBoost.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
noncomputable section
namespace GlobalTheory
namespace MatrixBall
section general
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
end general
section hermitian
variable {n : Type*} [Fintype n] [DecidableEq n]
end hermitian
section boost
variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]
def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)⁻¹
def boost (Z : Matrix p q ℂ) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  fromBlocks (invSqrt (1 - Z * Zᴴ)) (Z * invSqrt (1 - Zᴴ * Z))
    (Zᴴ * invSqrt (1 - Z * Zᴴ)) (invSqrt (1 - Zᴴ * Z))
section invSqrt
variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}
end invSqrt
variable {Z : Matrix p q ℂ}
end boost
end MatrixBall
end GlobalTheory


