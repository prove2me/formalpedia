-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExt
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapTwoSidedMulHaarMatrixQuadraticExt
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:57:20.040159+00:00
-- url     : https://prove2.me/theorems/3c386103-17a5-460f-b78c-d9efc3966be7
-- title:
--   Map Two Sided Mul Haar Matrix Quadratic Ext
-- statement:
--   Definitions and structural lemmas for Map Two Sided Mul Haar Matrix Quadratic Ext, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapTwoSidedMulHaarMatrixQuadraticExt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetRestrictScalarsTwoSidedMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapLinearEquivAddHaarLocalFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuadExtTopologyStatement
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
namespace GlobalTheory.KSp
noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]
end GlobalTheory.KSp


