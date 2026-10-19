-- Prove2me | Definitions.Def_MazurTransfer_Order13GeometricGenericEmbeddingBaseChangeData
-- name    : MazurTransfer_Order13GeometricGenericEmbeddingBaseChangeData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:23:12.789735+00:00
-- url     : https://prove2.me/theorems/e899a269-0ae4-4727-8406-5d761688d8d2
-- title:
--   The actual generic-stalk embedding commutes with extension of the base field
-- statement:
--   For every characteristic-zero field K, the original coordinate and function-field base-change maps commute, and the actual generic-stalk map of the literal K-curve followed by the actual curve base-change map equals Spec of the function-field extension followed by the rational generic-stalk map. Both complete original theorem types and the original local scalar algebra provider are compared. Named downstream consumer: geometric diamond curve base-change naturality.
-- source:
--   Complete original MazurTheorem Order13GeometricGenericEmbeddingBaseChange with the accepted affine-chart generic-stalk lemma and published original coordinate, curve, function-field and generic lift maps. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal curve base-change map and the injective
function-field extension commute with the actual generic-stalk maps.
Named downstream consumer: base-change naturality of the diamond curve lift.
-/
import Definitions.Def_MazurTransfer_Order13GeometricFunctionFieldBaseChangePublishedCoordinateMaps20261017
import Theorems.Thm_MazurTransfer_AffineOpenChartGenericEmbeddingCompatibility_coordinateEmbedding_generic
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
import Definitions.Def_MazurTransfer_Order13FieldCurveAutomorphismLiftData

noncomputable section
namespace MazurTransfer.Order13GeometricGenericEmbeddingBaseChange
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open AffineOpenChartFunctionField
open Order13ActualCurveBaseChange Order13GeometricFunctionFieldBaseChange
open Order13FieldCurveAutomorphismLift
variable (K : Type) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _

theorem coordinate_baseChange :
    CommRingCat.ofHom (coordinateEmbedding (CommRingCat.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ)) ≫
      CommRingCat.ofHom (fieldBaseChange K) =
    CommRingCat.ofHom (Order13CoordinateBaseChange.ordinaryRingMap ℚ K) ≫
      CommRingCat.ofHom (coordinateEmbedding (CommRingCat.of (CoordinateRing K)) (ordinaryChartMap K)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  exact fieldBaseChange_coordinate K b

theorem genericEmbedding_baseChange :
    genericEmbedding K ≫ curveMap ℚ K =
      Spec.map (CommRingCat.ofHom (fieldBaseChange K)) ≫ genericEmbedding ℚ := by
  change (curveScheme K).fromSpecStalk (genericPoint (curveScheme K)) ≫ curveMap ℚ K =
    Spec.map (CommRingCat.ofHom (fieldBaseChange K)) ≫
      (curveScheme ℚ).fromSpecStalk (genericPoint (curveScheme ℚ))
  rw [← MazurTransfer.AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic (CommRingCat.of (CoordinateRing K)) (ordinaryChartMap K),
    Category.assoc, ordinaryChartMap_curveMap, ← Spec.map_comp_assoc]
  rw [← MazurTransfer.AffineOpenChartGenericEmbeddingCompatibility.coordinateEmbedding_generic (CommRingCat.of (CoordinateRing ℚ)) (ordinaryChartMap ℚ),
    ← Spec.map_comp_assoc, coordinate_baseChange]

end MazurTransfer.Order13GeometricGenericEmbeddingBaseChange
#print axioms MazurTransfer.Order13GeometricGenericEmbeddingBaseChange.genericEmbedding_baseChange


