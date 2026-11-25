-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycle
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgebraPullbackTwoConvMulSymmetricCocycle
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:36:46.393621+00:00
-- url     : https://prove2.me/theorems/84fed840-d8d1-4008-a1be-1fb891f7245e
-- title:
--   Bialgebra Pullback Two Conv Mul Symmetric Cocycle
-- statement:
--   Definitions and structural lemmas for Bialgebra Pullback Two Conv Mul Symmetric Cocycle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgebraPullbackTwoConvMulSymmetricCocycle.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv
namespace GlobalTheory
namespace PDiv
namespace CocycleSum
variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]
def val (x y : WithConv (A →ₐ[R] X)) : A ⊗[R] A →ₐ[R] X :=
  Algebra.TensorProduct.lift x.ofConv y.ofConv fun _ _ => .all ..
variable {B : Type} [CommRing B] [Bialgebra R B]
end CocycleSum
end PDiv
end GlobalTheory


