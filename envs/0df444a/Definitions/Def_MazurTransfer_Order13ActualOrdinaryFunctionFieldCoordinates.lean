-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualOrdinaryFunctionFieldCoordinates
-- name    : MazurTransfer_Order13ActualOrdinaryFunctionFieldCoordinates
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T09:54:29.795454+00:00
-- url     : https://prove2.me/theorems/a40c70a2-ff75-4d50-970a-15ba792b53ca
-- title:
--   The original ordinary coordinate algebra inside the literal order-thirteen function field
-- statement:
--   Let $K$ be a field of characteristic zero and let $X/K$ be the specified order-thirteen curve. The actual ordinary affine chart gives a $\operatorname{CoordinateRing}(K)$-algebra structure on its existing scheme function field $K(X)$ and the specified fraction-ring structure. The actual coordinate elements are $$x=\iota(x_{\mathrm{coord}}),\qquad y=\iota(y_{\mathrm{coord}}),$$ where $\iota$ is the chart embedding defined through the generic-point stalk map. The coordinate-ring domain instance and the structural maps are retained. This supplies the literal coordinates for the rational diamond function-field automorphism.
-- source:
--   Five original complete declarations from MazurTheorem Order13ChartOverlapFunctionField.lean (ordinaryRing_isDomain, ordinaryFunctionFieldAlgebra and ordinaryFunctionField_isFractionRing) and Order13PellActualOrdinaryChart.lean (xImage and yImage), Apache-2.0, Vas and contributors. All five bodies are unchanged, with explicit public geometry, primitive aliases and the original affine-chart fraction-field construction. Five original closed types and three data values are kernel-compared; the domain and fraction-ring instances are proof-valued. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual rational diamond field automorphism.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: original ordinary chart algebra and coordinates in the
literal scheme function field, with the original fraction-ring structure.
Named downstream consumer: the actual rational diamond field automorphism. -/
import Mathlib
import Definitions.Def_MazurTransfer_AffineOpenChartFunctionField
import Definitions.Def_MazurTransfer_Order13GoodCharacteristicPlaceFoundation
import Definitions.Def_MazurTransfer_Order13CanonicalFiniteMapPrimitives
noncomputable section
universe u
namespace MazurTransfer.Order13ChartOverlapFunctionField
open AlgebraicGeometry CategoryTheory
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.AffineOpenChartFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
instance ordinaryRing_isDomain : IsDomain (CoordinateRing K) :=
  Order13ReciprocalInjectionCurveDomains.coordinateRing_isDomain K
    (isUnit_iff_ne_zero.mpr (by norm_num))

instance ordinaryFunctionFieldAlgebra : Algebra (CoordinateRing K) (actualCurveFunctionField K) :=
  coordinateAlgebra (.of (CoordinateRing K)) (ordinaryChartMap K)

instance ordinaryFunctionField_isFractionRing :
    IsFractionRing (CoordinateRing K) (actualCurveFunctionField K) :=
  coordinate_isFractionRing (.of (CoordinateRing K)) (ordinaryChartMap K)
end MazurTransfer.Order13ChartOverlapFunctionField
namespace MazurTransfer.Order13PellActualOrdinaryChart
open MazurTorsion.XOneThirteenProjectiveCurve MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open MazurTransfer.Order13ChartOverlapFunctionField
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
def xImage : actualCurveFunctionField K :=
  algebraMap (CoordinateRing K) (actualCurveFunctionField K) (xCoordinate K)

def yImage : actualCurveFunctionField K :=
  algebraMap (CoordinateRing K) (actualCurveFunctionField K) (yCoordinate K)
end MazurTransfer.Order13PellActualOrdinaryChart
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.ordinaryFunctionFieldAlgebra
#print axioms MazurTransfer.Order13ChartOverlapFunctionField.ordinaryFunctionField_isFractionRing


