-- Prove2me | Definitions.Def_MazurTransfer_Order13GeometricInverseDiamondCurveNaturalityData
-- name    : MazurTransfer_Order13GeometricInverseDiamondCurveNaturalityData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:38:48.524986+00:00
-- url     : https://prove2.me/theorems/3a17552b-350a-474b-99f0-b1d327b89e4c
-- title:
--   The inverse diamond lifts commute with the actual extension-field curve map
-- statement:
--   For every characteristic-zero field, the inverse of the chosen generic-compatible diamond curve lift commutes with the actual curve map to Q and the inverse of the existing rational diamond lift. The full original statement and proof are retained and compared. Named downstream consumer: actual geometric Picard inverse-curve line-bundle pullback.
-- source:
--   Complete original MazurTheorem Order13GeometricInverseDiamondCurveNaturality.existingDiamondCurve_inverse_baseChange, using the published compatibility with the existing rational chosen lift. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse diamond lifts commute with the actual curve map
from every characteristic-zero extension field to Q. Named downstream
consumer: geometric point line bundles of the rational Picard action.
-/
import Definitions.Def_MazurTransfer_Order13RationalGenericCurveLiftCompatibilityData

noncomputable section
namespace MazurTransfer.Order13GeometricInverseDiamondCurveNaturality
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem existingDiamondCurve_inverse_baseChange :
    (Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K).inv ≫
      Order13ActualCurveBaseChange.curveMap ℚ K =
    Order13ActualCurveBaseChange.curveMap ℚ K ≫
      Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso.inv := by
  let e : curveScheme K ≅ curveScheme K := Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K
  let d : curveScheme ℚ ≅ curveScheme ℚ := Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso
  let b := Order13ActualCurveBaseChange.curveMap ℚ K
  change e.inv ≫ b = b ≫ d.inv
  apply (cancel_epi e.hom).mp
  have h : e.hom ≫ b = b ≫ d.hom :=
    Order13RationalGenericCurveLiftCompatibility.existingDiamondCurve_baseChange K
  rw [← Category.assoc, e.hom_inv_id, Category.id_comp, ← Category.assoc, h,
    Category.assoc, d.hom_inv_id, Category.comp_id]

end MazurTransfer.Order13GeometricInverseDiamondCurveNaturality
#print axioms MazurTransfer.Order13GeometricInverseDiamondCurveNaturality.existingDiamondCurve_inverse_baseChange


