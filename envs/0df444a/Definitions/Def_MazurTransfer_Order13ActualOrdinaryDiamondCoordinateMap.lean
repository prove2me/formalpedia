-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualOrdinaryDiamondCoordinateMap
-- name    : MazurTransfer_Order13ActualOrdinaryDiamondCoordinateMap
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T10:33:38.189723+00:00
-- url     : https://prove2.me/theorems/7e271e5b-e321-47b8-8608-d6d9b048eac7
-- title:
--   The actual diamond coordinate homomorphism on the ordinary chart
-- statement:
--   Let $X/\mathbb Q$ be the literal order-thirteen curve and let $\mathbb Q(X)$ be its actual scheme function field, with the original ordinary coordinates $x$ and $y$. The diamond substitution defines a ring homomorphism from the actual ordinary coordinate ring by $$x_{\mathrm{coord}}\longmapsto-\frac1{x+1},\qquad y_{\mathrm{coord}}\longmapsto\frac{y}{(x+1)^3}.$$ The defining quadratic relation is satisfied in the actual function field, and the original polynomial and coordinate evaluation formulas are retained. Injectivity and extension to the field are separate steps. This supplies the actual ordinary diamond coordinate map.
-- source:
--   Six original complete declarations and bodies from MazurTheorem Order13ActualDiamondFunctionFieldMap.lean: yImage_sq, diamond_root, ordinaryDiamond, ordinaryDiamond_polynomial, ordinaryDiamond_x and ordinaryDiamond_y. Apache-2.0, Vas and contributors. Only public imports change; the injection and field-extension declarations are separate. Six original closed types and the single ordinary coordinate-map data value are kernel-compared; native, strict and complete frontend checks pass with standard axioms only. Named downstream consumers: actual ordinary diamond injection and rational diamond field endomorphism.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal order-six coordinate substitution extends
injectively to the actual rational scheme function field. Named downstream
consumer: its inverse, exact order, and action on actual arithmetic Picard
classes in the nineteen-isogeny descent.
-/
import Definitions.Def_MazurTransfer_Order13DiamondSexticCoordinateTransform
import Definitions.Def_MazurTransfer_Order13ActualOrdinaryPolynomialTranscendence

noncomputable section
namespace MazurTransfer.Order13ActualDiamondFunctionFieldMap
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13DiamondSexticSymmetry Order13ActualOrdinaryPolynomialTranscendence
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem yImage_sq : yImage ℚ ^ 2 = Order13PellChartCertificate.sextic (xImage ℚ) := by
  have H := congrArg (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)) (yCoordinate_sq ℚ)
  simpa only [sexticPolynomial, Order13PellChartCertificate.sextic,
    map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X, xImage, yImage] using H

theorem diamond_root :
    (affineEquation ℚ).eval₂ (aeval (diamondX (xImage ℚ))).toRingHom
      (diamondY (xImage ℚ) (yImage ℚ)) = 0 := by
  have H := preserves_curve (xImage ℚ) (yImage ℚ) xImage_add_one_ne_zero yImage_sq
  simp only [affineEquation, eval₂_sub, eval₂_X_pow, eval₂_C]
  apply sub_eq_zero.mpr
  change diamondY (xImage ℚ) (yImage ℚ) ^ 2 =
    aeval (diamondX (xImage ℚ)) (sexticPolynomial ℚ)
  simpa only [sexticPolynomial, Order13PellChartCertificate.sextic,
    map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X] using H

def ordinaryDiamond : CoordinateRing ℚ →+* actualCurveFunctionField ℚ :=
  AdjoinRoot.lift (aeval (diamondX (xImage ℚ))).toRingHom
    (diamondY (xImage ℚ) (yImage ℚ)) diamond_root

theorem ordinaryDiamond_polynomial (p : Polynomial ℚ) :
    ordinaryDiamond (AdjoinRoot.of (affineEquation ℚ) p) =
      aeval (diamondX (xImage ℚ)) p := AdjoinRoot.lift_of diamond_root

theorem ordinaryDiamond_x : ordinaryDiamond (xCoordinate ℚ) = diamondX (xImage ℚ) := by
  rw [xCoordinate, ordinaryDiamond_polynomial, aeval_X]

theorem ordinaryDiamond_y : ordinaryDiamond (yCoordinate ℚ) = diamondY (xImage ℚ) (yImage ℚ) :=
  AdjoinRoot.lift_root diamond_root











end MazurTransfer.Order13ActualDiamondFunctionFieldMap
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldMap.ordinaryDiamond
#print axioms MazurTransfer.Order13ActualDiamondFunctionFieldMap.diamond_root


