-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualGenusTwoCurveModelOriginalCompleteTelescopeV2Data20261018
-- name    : MazurTransfer_Order13ActualGenusTwoCurveModelOriginalCompleteTelescopeV2Data20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T13:01:16.02277+00:00
-- url     : https://prove2.me/theorems/b9586078-aa1e-4921-bf48-036a66e129c9
-- title:
--   Original literal genus-two curve model
-- statement:
--   The original literal genus-two CurveModel constructor is preserved through the existing actual arithmetic curve model, with its complete original telescope and nonproof value checked. The named downstream consumer is the actual geometric semilinear Galois lift.
-- source:
--   MazurTheorem original checked constructors and complete type/value audits; official FLT provenance retained where used.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: preserve the original literal genus-two CurveModel
constructor through the existing public actual arithmetic CurveModel.
Named downstream consumer: the actual geometric semilinear Galois lift
and its divisor-class compatibility for the actual nineteen pairing. -/
import Definitions.Def_MazurTransfer_Order13ActualCurveModel
noncomputable section
universe u
namespace MazurTransfer.Order13ActualGenusTwoCurveModel
open AlgebraicCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
def actualCurveModel (K : Type u) [Field K]
    [Fact ((104 : K) ≠ 0)] [IsAlgClosed K] : CurveModel K (actualCurveFunctionField K) :=
  Order13ActualArithmeticCurveModel.actualCurveModel K
end MazurTransfer.Order13ActualGenusTwoCurveModel
#print axioms MazurTransfer.Order13ActualGenusTwoCurveModel.actualCurveModel


