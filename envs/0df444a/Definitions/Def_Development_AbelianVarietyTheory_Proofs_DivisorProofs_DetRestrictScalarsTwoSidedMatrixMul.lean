-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMul
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T21:10:59.288464+00:00
-- url     : https://prove2.me/theorems/5b1249d5-453b-4c76-b795-7cdf57496b4e
-- title:
--   Det Restrict Scalars Two Sided Matrix Mul
-- statement:
--   Definitions and structural lemmas for Det Restrict Scalars Two Sided Matrix Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetRestrictScalarsTwoSidedMatrixMul.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
noncomputable section
namespace GlobalTheory.KSp
def twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [Fintype ν]
    (u : Matrix α α E) (a : Matrix ν ν E) : Matrix α ν E →ₗ[E] Matrix α ν E where
  toFun x := u * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
end GlobalTheory.KSp


