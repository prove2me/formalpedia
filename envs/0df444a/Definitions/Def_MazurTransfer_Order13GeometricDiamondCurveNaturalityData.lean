-- Prove2me | Definitions.Def_MazurTransfer_Order13GeometricDiamondCurveNaturalityData
-- name    : MazurTransfer_Order13GeometricDiamondCurveNaturalityData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:29:51.504518+00:00
-- url     : https://prove2.me/theorems/09097a95-5a2b-497b-93e8-25696c03cc81
-- title:
--   The actual generic diamond curve lift commutes with extension of the base field
-- statement:
--   The original rational and general diamond substitutions agree at Q, their field-base-change maps commute in both directions, their Spec maps commute, and the actual generic diamond curve lifts commute with the literal curve base-change map. Six original types, including the original base-map compatibility bridge, and both local scalar algebra providers are compared. Named downstream consumer: compatibility with the existing rational Picard diamond and its inverse.
-- source:
--   Complete original MazurTheorem geometric diamond/closed-point transport statements and proofs, with public original map and isomorphism constructors. The original base-map compatibility statement is a checked bridge from the accepted Cartesian-square theorem. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual diamond curve lift over a characteristic-zero
extension field commutes with the literal base-change map from the curve
 over Q. Named downstream consumer: comparison of the rational represented
Picard diamond with its geometric field action.
-/
import Definitions.Def_MazurTransfer_Order13GeometricGenericEmbeddingBaseChangeData
import Definitions.Def_MazurTransfer_Order13FieldDiamondGenericCurveOrderData

import Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
noncomputable section
universe u
namespace MazurTransfer.Order13ActualCurveBaseChange
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
theorem curveMap_base (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    curveMap R S ≫ curveToBase R = curveToBase S ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  (wholeCurve_isPullback R S).w
end MazurTransfer.Order13ActualCurveBaseChange
end
noncomputable section
namespace MazurTransfer.Order13GeometricDiamondCurveNaturality
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13PellActualOrdinaryChart
open Order13GeometricFunctionFieldBaseChange Order13GeometricGenericEmbeddingBaseChange
open Order13ActualCurveBaseChange Order13FieldCurveAutomorphismLift
open Order13FieldDiamondFunctionFieldAutomorphism Order13FieldDiamondGenericCurveOrder
variable (K : Type) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : CharZero (actualCurveFunctionField K) := Algebra.charZero_of_charZero K _
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem diamondRational_agrees :
    Order13FieldDiamondFunctionFieldMap.diamondFieldMap ℚ =
      Order13ActualDiamondFunctionFieldMap.diamondFieldMap := by
  apply rationalFieldMap_ext_xy ℚ
  · rw [Order13FieldDiamondFunctionFieldMap.diamondFieldMap_x,
      Order13ActualDiamondFunctionFieldMap.diamondFieldMap_x]
  · rw [Order13FieldDiamondFunctionFieldMap.diamondFieldMap_y,
      Order13ActualDiamondFunctionFieldMap.diamondFieldMap_y]

theorem fieldBaseChange_diamond_general :
    (fieldBaseChange K).comp (diamondAlgEquiv ℚ).toRingHom =
      (diamondAlgEquiv K).toRingHom.comp (fieldBaseChange K) := by
  change (fieldBaseChange K).comp (Order13FieldDiamondFunctionFieldMap.diamondFieldMap ℚ) =
      (Order13FieldDiamondFunctionFieldMap.diamondFieldMap K).comp (fieldBaseChange K)
  rw [diamondRational_agrees]
  exact fieldBaseChange_diamond K

theorem fieldBaseChange_diamond_symm :
    (fieldBaseChange K).comp (diamondAlgEquiv ℚ).symm.toRingHom =
      (diamondAlgEquiv K).symm.toRingHom.comp (fieldBaseChange K) := by
  ext b
  change fieldBaseChange K ((diamondAlgEquiv ℚ).symm b) =
    (diamondAlgEquiv K).symm (fieldBaseChange K b)
  apply (diamondAlgEquiv K).injective
  have h := RingHom.congr_fun (fieldBaseChange_diamond_general K) ((diamondAlgEquiv ℚ).symm b)
  change fieldBaseChange K ((diamondAlgEquiv ℚ) ((diamondAlgEquiv ℚ).symm b)) =
      (diamondAlgEquiv K) (fieldBaseChange K ((diamondAlgEquiv ℚ).symm b)) at h
  exact h.symm.trans ((congrArg (fieldBaseChange K) ((diamondAlgEquiv ℚ).apply_symm_apply b)).trans
    ((diamondAlgEquiv K).apply_symm_apply (fieldBaseChange K b)).symm)

theorem diamondSpec_commute :
    Spec.map (CommRingCat.ofHom (diamondAlgEquiv K).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (fieldBaseChange K)) =
    Spec.map (CommRingCat.ofHom (fieldBaseChange K)) ≫
      Spec.map (CommRingCat.ofHom (diamondAlgEquiv ℚ).symm.toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (fieldBaseChange_diamond_symm K).symm)

theorem diamondCurve_baseChange :
    (genericDiamondCurveIso K).hom ≫ curveMap ℚ K =
      curveMap ℚ K ≫ (genericDiamondCurveIso ℚ).hom := by
  dsimp only [genericDiamondCurveIso]
  apply Scheme.Hom.eq_of_fromSpecStalk_genericPoint_comp_eq
    (curveToBase K ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) (curveToBase ℚ)
  · rw [Category.assoc, curveMap_base, ← Category.assoc, fieldLift_over]
  · rw [Category.assoc, fieldLift_over, curveMap_base]
  · change genericEmbedding K ≫ ((fieldLift K (diamondAlgEquiv K)).hom ≫ curveMap ℚ K) =
      genericEmbedding K ≫ (curveMap ℚ K ≫ (fieldLift ℚ (diamondAlgEquiv ℚ)).hom)
    rw [← Category.assoc, fieldLift_generic, Category.assoc, genericEmbedding_baseChange,
      ← Category.assoc, diamondSpec_commute, Category.assoc, ← fieldLift_generic,
      ← Category.assoc, ← genericEmbedding_baseChange, Category.assoc]

end MazurTransfer.Order13GeometricDiamondCurveNaturality
#print axioms MazurTransfer.Order13GeometricDiamondCurveNaturality.diamondCurve_baseChange


