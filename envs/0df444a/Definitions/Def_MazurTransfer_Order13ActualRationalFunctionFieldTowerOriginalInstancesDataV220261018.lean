-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
-- name    : MazurTransfer_Order13ActualRationalFunctionFieldTowerOriginalInstancesDataV220261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T07:58:37.455626+00:00
-- url     : https://prove2.me/theorems/8f3250f3-b515-4edb-ae6b-912e25b0ea57
-- title:
--   The actual order-13 rational-function-field tower with its original algebra
-- statement:
--   For any field K of characteristic zero, define the original embedding of RatFunc K into the actual order-13 curve function field by the existing equivalence RatFunc K ≃ K(x), followed by inclusion of K(x). Retain its original induced RatFunc K algebra and the original characteristic and base-field algebra instances. This interface supplies the finite rational-function-field tower used by the divisibility proof of injectivity of the actual divisorial nineteen-pairing; scalar-tower compatibility and finite-dimensionality are separate checked theorem contracts.
-- source:
--   MazurTheorem, Order13ActualRationalFunctionFieldTower.lean; Apache-2.0. The two original definitions and their nonproof values, two original source providers, and five existing hyperelliptic-field dependency providers have been compared against their complete original Lean types and values.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual order-13 function field is finite over the
rational function field via its existing transcendental x-coordinate.
Named downstream consumer: instantiate the divisibility-based injectivity
theorem for the actual divisorial nineteen-pairing.
-/
import Definitions.Def_MazurTransfer_Order13FieldHyperellipticFixedFieldData

noncomputable section
namespace MazurTransfer.Order13ActualRationalFunctionFieldTower
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13FieldHyperellipticFixedField
variable (K : Type*) [Field K] [CharZero K]
local instance actualRatFuncTowerOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance actualRatFuncTowerOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def actualRatFuncEmbedding : RatFunc K →ₐ[K] actualCurveFunctionField K :=
  (xField K).val.comp (rationalInvolutionFieldEquiv K).toAlgHom

def actualRatFuncAlgebra : Algebra (RatFunc K) (actualCurveFunctionField K) :=
  (actualRatFuncEmbedding K).toRingHom.toAlgebra


end MazurTransfer.Order13ActualRationalFunctionFieldTower

#print axioms MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalFactProvider20261018
#print axioms MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFuncTowerOriginalAlgebraProvider20261018
#print axioms MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFuncEmbedding
#print axioms MazurTransfer.Order13ActualRationalFunctionFieldTower.actualRatFuncAlgebra


