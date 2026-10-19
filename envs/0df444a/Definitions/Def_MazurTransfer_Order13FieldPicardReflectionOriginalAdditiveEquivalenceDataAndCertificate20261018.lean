-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldPicardReflectionOriginalAdditiveEquivalenceDataAndCertificate20261018
-- name    : MazurTransfer_Order13FieldPicardReflectionOriginalAdditiveEquivalenceDataAndCertificate20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T21:26:55.174396+00:00
-- url     : https://prove2.me/theorems/07aec2a7-8e1c-437d-9a0e-57d735f67d8f
-- title:
--   Original additive Picard reflection equivalence
-- statement:
--   The original involutive function-field reflection acts through the Anthropic FLT divisor-class action and constructs the original additive equivalence of the actual arithmetic Picard group. Two complete original declaration types and the whole additive-equivalence value are checked, including three own instance-provider types and one value, seven context-provider types and three values, and the exact square certificate required by the constructor. Named downstream consumer: MazurTransfer.Order13ActualNineteenTorsionReflection.divisorTorsionReflection. The substantive identities exchanging the two norm maps remain separate theorems.
-- source:
--   MazurTheorem Order13FieldPicardReflection.reflection and reflection_apply, with the original structural function-field square certificate from Order13ActualReflectionDiamondRelation; original official Anthropic FLT Picard action preserved; Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Uses the complete checked divisor-class action from Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: the literal reflection acts involutively on actual arithmetic
Pic0 and exchanges its two nineteen-norm endomorphisms. Named downstream
consumer: MazurTransfer.Order13ActualNineteenTorsionReflection.divisorTorsionReflection.
-/
import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualReflectionFunctionFieldOriginalDataAndConstructorCertificates20261018
import Definitions.Def_MazurTransfer_Order13FieldDiamondPicardEndomorphismsData
noncomputable section
universe u
namespace MazurTransfer.ReflectionPicardConstructorProofHelpers20261018
open Order13ReflectionParameter Order13ActualReflectionFunctionField
open Order13FieldDiamondFunctionFieldAutomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type u) [Field K] [CharZero K]
theorem reflectionAlgEquiv_square (a : ReflectionParameter K) :
    reflectionAlgEquiv K a * reflectionAlgEquiv K a = 1 := by
  ext z
  exact RingHom.congr_fun (reflectionFieldMap_square K a) z
end MazurTransfer.ReflectionPicardConstructorProofHelpers20261018

namespace MazurTransfer.Order13FieldPicardReflection
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ReflectionParameter Order13ActualReflectionFunctionField ReflectionPicardConstructorProofHelpers20261018
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondPicardEndomorphisms
variable (K : Type u) [Field K] [CharZero K]
local instance fieldPicardReflectionOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance fieldPicardReflectionOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance fieldPicardReflectionOriginalCharZeroProvider20261018 : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

def reflection (a : ReflectionParameter K) : ActualPicard K ≃+ ActualPicard K where
  toFun c := reflectionAlgEquiv K a • c
  invFun c := reflectionAlgEquiv K a • c
  left_inv c := by
    change reflectionAlgEquiv K a • (reflectionAlgEquiv K a • c) = c
    rw [← mul_smul, reflectionAlgEquiv_square K a, one_smul]
  right_inv c := by
    change reflectionAlgEquiv K a • (reflectionAlgEquiv K a • c) = c
    rw [← mul_smul, reflectionAlgEquiv_square K a, one_smul]
  map_add' c d := smul_add _ c d

theorem reflection_apply (a : ReflectionParameter K) (c : ActualPicard K) :
    reflection K a c = reflectionAlgEquiv K a • c := rfl

end MazurTransfer.Order13FieldPicardReflection
#print axioms MazurTransfer.Order13FieldPicardReflection.reflection


