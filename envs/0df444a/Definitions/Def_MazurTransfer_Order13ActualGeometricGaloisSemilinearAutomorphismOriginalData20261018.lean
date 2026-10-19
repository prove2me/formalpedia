-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
-- name    : MazurTransfer_Order13ActualGeometricGaloisSemilinearAutomorphismOriginalData20261018
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-18T13:02:59.21051+00:00
-- url     : https://prove2.me/theorems/9e842f05-bee6-40bc-a74a-0f137bb7f6ae
-- title:
--   Original actual geometric Galois semilinear function-field automorphism
-- statement:
--   Preserve the original geometric curve-model isomorphism and explicit actual semilinear Galois function-field lift, including its literal coefficient action, three complete original declaration types, two nonproof constructor values, and two field-provider types/one algebra value. The original twenty-two generic semilinear helper declarations are independently checked. The named downstream consumer is actual divisor-class Galois compatibility and covariance of the actual nineteen pairing.
-- source:
--   MazurTheorem original checked constructors and complete type/value audits; official FLT provenance retained where used.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: an explicit geometric semilinear function-field lift of
the actual curve Galois isomorphism has the correct coefficient action,
generic diagram and stalk-range transport.
Named downstream consumer: semilinear divisor presentations and unconditional
covariance of the SAME actual Picard pairing under Galois precomposition.
-/
import Definitions.Def_MazurTransfer_Order13ActualGenusTwoCurveModelOriginalCompleteTelescopeV2Data20261018
import Definitions.Def_MazurTransfer_Order13ActualGeometricCurveGaloisAutomorphismOriginalData20261018
import Definitions.Def_MazurTransfer_CurveModelGeometricSemilinearLiftOriginalData20261018

noncomputable section
namespace MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualGenusTwoCurveModel Order13ActualGeometricCurveGaloisAutomorphism
open MazurTransfer.CurveModelGeometricSemilinearLiftOriginalData20261018
variable (K : Type) [Field K] [CharZero K] [IsAlgClosed K]
local instance geometricGaloisOriginalFactProvider20261018 : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance geometricGaloisOriginalAlgebraProvider20261018 : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

def geometricModelIso (σ : K ≃ₐ[ℚ] K) : (actualCurveModel K).C ≅ (actualCurveModel K).C :=
  geometricCurveGaloisIso K σ

def geometricSemilinearAut (σ : K ≃ₐ[ℚ] K) : SemilinearAut K (actualCurveFunctionField K) :=
  gSL (actualCurveModel K) (geometricModelIso K σ) σ.toRingEquiv
    (geometricCurveGaloisIso_toBase K σ)

theorem geometricSemilinearAut_baseAut (σ : K ≃ₐ[ℚ] K) :
    SemilinearAut.baseAut (geometricSemilinearAut K σ) = σ.toRingEquiv := rfl

end MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism
#print axioms MazurTransfer.Order13ActualGeometricGaloisSemilinearAutomorphism.geometricSemilinearAut


