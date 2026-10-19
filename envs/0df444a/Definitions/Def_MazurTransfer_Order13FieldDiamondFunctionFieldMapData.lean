-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldMapData
-- name    : MazurTransfer_Order13FieldDiamondFunctionFieldMapData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T17:17:46.13463+00:00
-- url     : https://prove2.me/theorems/141ee5f1-5199-47ac-ba6f-a5496ec0f099
-- title:
--   The actual diamond coordinate map extends to the function field over characteristic-zero fields
-- statement:
--   The complete original diamond substitution, its integral-coordinate-ring lift, injectivity, extension to the actual scheme function field, coordinate formulas and preservation of structural scalars, over every characteristic-zero base field. Thirteen full original declaration types, both map constructor values and both the original current and dependency scalar algebra providers are checked. Named downstream consumer: the actual general-field diamond automorphism.
-- source:
--   Complete original MazurTheorem Order13FieldDiamondFunctionFieldMap with the original generic integral-injectivity and fractional-linear transcendence helper proofs. Public characteristic-zero coordinate inputs and literal sextic transform. Official Anthropic FLT interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal order-six coordinate substitution extends
injectively to the actual scheme function field over every characteristic-zero field. Named downstream
consumer: its inverse, exact order, and action on actual arithmetic Picard
classes in the nineteen-isogeny descent.
-/

import Definitions.Def_MazurTransfer_Order13DiamondSexticCoordinateTransform
import Definitions.Def_MazurTransfer_Order13FieldOrdinaryPolynomialTranscendenceData

noncomputable section
universe u v w
namespace MazurTransfer.FieldDiamondMapPublicHelpers20261017
open Order13DiamondSexticSymmetry
theorem injective_of_integral (R : Type u) [CommRing R] [Nontrivial R]
    (A : Type v) [CommRing A] [IsDomain A] [Algebra R A] [Algebra.IsIntegral R A]
    (B : Type w) [CommRing B] (f : A →+* B)
    (h : Function.Injective (f.comp (algebraMap R A))) : Function.Injective f := by
  apply (RingHom.injective_iff_ker_eq_bot f).mpr
  apply Ideal.eq_bot_of_comap_eq_bot (R := R)
  change RingHom.ker (f.comp (algebraMap R A)) = ⊥
  exact (RingHom.injective_iff_ker_eq_bot _).mp h

theorem transcendental_diamondX {F : Type u} [Field F] (K : Type v) [Field K] [Algebra K F]
    (x : F) (hx : Transcendental K x) : Transcendental K (diamondX x) := by
  have hden : x + 1 ≠ 0 := by
    intro H
    have Hx : x = -1 := by linear_combination H
    apply hx
    rw [Hx]
    exact isIntegral_one.neg.isAlgebraic
  intro H
  apply hx
  rw [inverse_expression x hden]
  exact (H.inv.isIntegral.neg.sub isIntegral_one).isAlgebraic

end MazurTransfer.FieldDiamondMapPublicHelpers20261017
end
noncomputable section
universe u
namespace MazurTransfer.Order13FieldDiamondFunctionFieldMap
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13DiamondSexticSymmetry Order13FieldOrdinaryPolynomialTranscendence
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem yImage_sq : yImage K ^ 2 = Order13PellChartCertificate.sextic (xImage K) := by
  have H := congrArg (algebraMap (CoordinateRing K) (actualCurveFunctionField K)) (yCoordinate_sq K)
  simpa only [sexticPolynomial, Order13PellChartCertificate.sextic,
    map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X, xImage, yImage] using H

theorem diamond_root :
    (affineEquation K).eval₂ (aeval (diamondX (xImage K))).toRingHom
      (diamondY (xImage K) (yImage K)) = 0 := by
  have H := preserves_curve (xImage K) (yImage K) (xImage_add_one_ne_zero K) (yImage_sq K)
  simp only [affineEquation, eval₂_sub, eval₂_X_pow, eval₂_C]
  apply sub_eq_zero.mpr
  change diamondY (xImage K) (yImage K) ^ 2 =
    aeval (diamondX (xImage K)) (sexticPolynomial K)
  simpa only [sexticPolynomial, Order13PellChartCertificate.sextic,
    map_add, map_mul, map_pow, map_ofNat, map_one, aeval_X] using H

def ordinaryDiamond : CoordinateRing K →+* actualCurveFunctionField K :=
  AdjoinRoot.lift (aeval (diamondX (xImage K))).toRingHom
    (diamondY (xImage K) (yImage K)) (diamond_root K)

theorem ordinaryDiamond_polynomial (p : Polynomial K) :
    (ordinaryDiamond K) (AdjoinRoot.of (affineEquation K) p) =
      aeval (diamondX (xImage K)) p := AdjoinRoot.lift_of (diamond_root K)

theorem ordinaryDiamond_x : (ordinaryDiamond K) (xCoordinate K) = diamondX (xImage K) := by
  rw [xCoordinate, (ordinaryDiamond_polynomial K), aeval_X]

theorem ordinaryDiamond_y : (ordinaryDiamond K) (yCoordinate K) = diamondY (xImage K) (yImage K) :=
  AdjoinRoot.lift_root (diamond_root K)

theorem ordinaryDiamond_injective : Function.Injective (ordinaryDiamond K) := by
  let : Algebra.IsIntegral (Polynomial K) (CoordinateRing K) := (ordinary_isIntegral K)
  apply FieldDiamondMapPublicHelpers20261017.injective_of_integral (Polynomial K) (CoordinateRing K)
    (actualCurveFunctionField K) (ordinaryDiamond K)
  have H : (ordinaryDiamond K).comp (algebraMap (Polynomial K) (CoordinateRing K)) =
      (aeval (diamondX (xImage K))).toRingHom := by
    apply RingHom.ext
    intro p
    exact (ordinaryDiamond_polynomial K) p
  rw [H]
  exact transcendental_iff_injective.mp (FieldDiamondMapPublicHelpers20261017.transcendental_diamondX K (xImage K) (xImage_transcendental K))

def diamondFieldMap : actualCurveFunctionField K →+* actualCurveFunctionField K :=
  IsFractionRing.lift (ordinaryDiamond_injective K)

theorem diamondFieldMap_coordinate (b : CoordinateRing K) :
    (diamondFieldMap K) (algebraMap (CoordinateRing K) (actualCurveFunctionField K) b) = (ordinaryDiamond K) b :=
  IsFractionRing.lift_algebraMap (ordinaryDiamond_injective K) b

theorem diamondFieldMap_x : (diamondFieldMap K) (xImage K) = diamondX (xImage K) :=
  ((diamondFieldMap_coordinate K) (xCoordinate K)).trans (ordinaryDiamond_x K)

theorem diamondFieldMap_y : (diamondFieldMap K) (yImage K) = diamondY (xImage K) (yImage K) :=
  ((diamondFieldMap_coordinate K) (yCoordinate K)).trans (ordinaryDiamond_y K)

theorem ordinaryDiamond_algebraMap (r : K) :
    ordinaryDiamond K (algebraMap K (CoordinateRing K) r) = algebraMap K (actualCurveFunctionField K) r := by
  change ordinaryDiamond K (AdjoinRoot.of (affineEquation K) (Polynomial.C r)) = _
  rw [ordinaryDiamond_polynomial K, aeval_C]

theorem diamondFieldMap_algebraMap (r : K) :
    diamondFieldMap K (algebraMap K (actualCurveFunctionField K) r) =
      algebraMap K (actualCurveFunctionField K) r := by
  calc
    _ = diamondFieldMap K (algebraMap (CoordinateRing K) (actualCurveFunctionField K)
      (algebraMap K (CoordinateRing K) r)) :=
        congrArg (diamondFieldMap K) (ordinaryEmbedding_algebraMap K r).symm
    _ = ordinaryDiamond K (algebraMap K (CoordinateRing K) r) := diamondFieldMap_coordinate K _
    _ = _ := ordinaryDiamond_algebraMap K r

end MazurTransfer.Order13FieldDiamondFunctionFieldMap
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldMap.ordinaryDiamond_injective
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldMap.diamondFieldMap_x
#print axioms MazurTransfer.Order13FieldDiamondFunctionFieldMap.diamondFieldMap_y


