-- Prove2me | Definitions.Def_MazurTransfer_Order13GeometricFunctionFieldBaseChangePublishedCoordinateMaps20261017
-- name    : MazurTransfer_Order13GeometricFunctionFieldBaseChangePublishedCoordinateMaps20261017
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:19:23.641063+00:00
-- url     : https://prove2.me/theorems/61bf6af3-2cfd-4307-a84b-d4c4b8f6270d
-- title:
--   The actual rational function field embeds into each characteristic-zero curve function field compatibly with diamond
-- statement:
--   The original coordinate change of base induces an injective ring map from the actual rational scheme function field into the actual curve function field over every characteristic-zero field. The map preserves both coordinates and commutes with the literal diamond substitutions; equality of maps out of the rational field is detected on the two coordinates. Eleven original types, both map constructors and the original local scalar algebra provider are compared. Named downstream consumer: generic embedding base change and geometric diamond curve naturality.
-- source:
--   Complete original MazurTheorem Order13GeometricFunctionFieldBaseChange with the original integral injectivity argument, using public coordinate base-change maps and both actual diamond maps. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal coordinate change of base gives an injective
map of the actual rational function field into the actual extension-field
function field. It commutes with the diamond substitutions. Named downstream
consumer: geometric base-change compatibility of the actual curve/Picard action.
-/
import Definitions.Def_MazurTransfer_Order13FieldDiamondFunctionFieldAutomorphismData
import Definitions.Def_MazurTransfer_Order13ActualDiamondFunctionFieldAutomorphism
import Definitions.Def_MazurTransfer_Order13CoordinateBaseChangeMaps

noncomputable section
universe u
namespace MazurTransfer.Order13GeometricFunctionFieldBaseChange
open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart Order13ChartOverlapFunctionField
open Order13CoordinateBaseChange Order13DiamondSexticSymmetry
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

def ordinaryBaseFieldMap : CoordinateRing ℚ →+* actualCurveFunctionField K :=
  (algebraMap (CoordinateRing K) (actualCurveFunctionField K)).comp (ordinaryRingMap ℚ K)

theorem ordinaryBaseFieldMap_x : ordinaryBaseFieldMap K (xCoordinate ℚ) = xImage K := by
  change algebraMap (CoordinateRing K) (actualCurveFunctionField K) (ordinaryRingMap ℚ K (xCoordinate ℚ)) = _
  rw [ordinaryRingMap_x]
  rfl

theorem ordinaryBaseFieldMap_y : ordinaryBaseFieldMap K (yCoordinate ℚ) = yImage K := by
  change algebraMap (CoordinateRing K) (actualCurveFunctionField K) (ordinaryRingMap ℚ K (yCoordinate ℚ)) = _
  rw [ordinaryRingMap_y]
  rfl

theorem ordinaryBaseFieldMap_injective : Function.Injective (ordinaryBaseFieldMap K) := by
  let : Algebra.IsIntegral (Polynomial ℚ) (CoordinateRing ℚ) :=
    Order13FieldOrdinaryPolynomialTranscendence.ordinary_isIntegral ℚ
  apply FieldDiamondMapPublicHelpers20261017.injective_of_integral (Polynomial ℚ) (CoordinateRing ℚ)
    (actualCurveFunctionField K) (ordinaryBaseFieldMap K)
  have H : (ordinaryBaseFieldMap K).comp (algebraMap (Polynomial ℚ) (CoordinateRing ℚ)) =
      (aeval (R := ℚ) (xImage K)).toRingHom := by
    apply Polynomial.ringHom_ext'
    · exact Subsingleton.elim _ _
    · change ordinaryBaseFieldMap K (xCoordinate ℚ) = aeval (xImage K) X
      rw [aeval_X]
      exact ordinaryBaseFieldMap_x K
  rw [H]
  apply transcendental_iff_injective.mp
  exact (Order13FieldOrdinaryPolynomialTranscendence.xImage_transcendental K).restrictScalars
    (algebraMap ℚ K).injective

def fieldBaseChange : actualCurveFunctionField ℚ →+* actualCurveFunctionField K :=
  IsFractionRing.lift (ordinaryBaseFieldMap_injective K)

theorem fieldBaseChange_coordinate (b : CoordinateRing ℚ) :
    fieldBaseChange K (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ) b) =
      ordinaryBaseFieldMap K b := IsFractionRing.lift_algebraMap (ordinaryBaseFieldMap_injective K) b

theorem fieldBaseChange_x : fieldBaseChange K (xImage ℚ) = xImage K :=
  (fieldBaseChange_coordinate K (xCoordinate ℚ)).trans (ordinaryBaseFieldMap_x K)

theorem fieldBaseChange_y : fieldBaseChange K (yImage ℚ) = yImage K :=
  (fieldBaseChange_coordinate K (yCoordinate ℚ)).trans (ordinaryBaseFieldMap_y K)

theorem fieldBaseChange_injective : Function.Injective (fieldBaseChange K) :=
  (fieldBaseChange K).injective

theorem rationalFieldMap_ext_xy (f g : actualCurveFunctionField ℚ →+* actualCurveFunctionField K)
    (hx : f (xImage ℚ) = g (xImage ℚ)) (hy : f (yImage ℚ) = g (yImage ℚ)) : f = g := by
  apply IsFractionRing.ringHom_ext (A := CoordinateRing ℚ)
  have H : f.comp (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)) =
      g.comp (algebraMap (CoordinateRing ℚ) (actualCurveFunctionField ℚ)) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext'
      · exact Subsingleton.elim _ _
      · exact hx
    · exact hy
  exact fun b => RingHom.congr_fun H b

theorem fieldBaseChange_diamond :
    (fieldBaseChange K).comp Order13ActualDiamondFunctionFieldMap.diamondFieldMap =
      (Order13FieldDiamondFunctionFieldMap.diamondFieldMap K).comp (fieldBaseChange K) := by
  apply rationalFieldMap_ext_xy K
  · simp only [RingHom.comp_apply, Order13ActualDiamondFunctionFieldMap.diamondFieldMap_x,
      fieldBaseChange_x, Order13FieldDiamondFunctionFieldMap.diamondFieldMap_x,
      diamondX, map_div₀, map_neg, map_one, map_add]
  · simp only [RingHom.comp_apply, Order13ActualDiamondFunctionFieldMap.diamondFieldMap_y,
      fieldBaseChange_y, Order13FieldDiamondFunctionFieldMap.diamondFieldMap_y,
      diamondY, map_div₀, map_pow, map_add, map_one, fieldBaseChange_x]

end MazurTransfer.Order13GeometricFunctionFieldBaseChange
#print axioms MazurTransfer.Order13GeometricFunctionFieldBaseChange.fieldBaseChange_injective
#print axioms MazurTransfer.Order13GeometricFunctionFieldBaseChange.fieldBaseChange_diamond


