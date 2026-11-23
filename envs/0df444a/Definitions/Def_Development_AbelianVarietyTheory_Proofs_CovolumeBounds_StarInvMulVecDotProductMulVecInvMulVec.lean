-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
-- name    : Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:22.382747+00:00
-- url     : https://prove2.me/theorems/d2d8bc1c-529c-41c8-8010-670558956f02
-- title:
--   Star Inv Mul Vec Dot Product Mul Vec Inv Mul Vec
-- statement:
--   Definitions and structural lemmas for Star Inv Mul Vec Dot Product Mul Vec Inv Mul Vec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/StarInvMulVecDotProductMulVecInvMulVec.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
namespace GlobalTheory
section RCLike
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
variable [DecidableEq n]
section Gram
variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
end Gram
end RCLike
section Rational
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
open NumberField IsCMField
variable [NumberField K] [IsCMField K]
end Rational
end GlobalTheory


