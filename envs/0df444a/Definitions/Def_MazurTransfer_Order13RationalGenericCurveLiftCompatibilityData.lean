-- Prove2me | Definitions.Def_MazurTransfer_Order13RationalGenericCurveLiftCompatibilityData
-- name    : MazurTransfer_Order13RationalGenericCurveLiftCompatibilityData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:34:28.820616+00:00
-- url     : https://prove2.me/theorems/a5145d0f-adad-4e14-9dde-d1f1cdbb625c
-- title:
--   The general-field diamond lift at Q is the existing rational lift
-- statement:
--   The general field lift at Q equals the previously chosen rational curve lift, the two rational diamond algebra automorphisms agree, the chosen diamond curve isomorphisms agree, and the extension-field lift commutes with base change to that existing rational lift. All four original types and the original rational scalar algebra provider are compared. Named downstream consumer: geometric inverse-diamond naturality and action on the same rational Picard scheme.
-- source:
--   Complete original MazurTheorem Order13RationalGenericCurveLiftCompatibility, using the published generic diamond naturality and existing rational chosen lift. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: identify the general-field lift at Q with the previously
checked generic-compatible rational lift by its specified generic action.
Named downstream consumer: base-change compatibility for the existing
rational represented Picard action, without changing its choice of lift.
-/
import Definitions.Def_MazurTransfer_Order13GeometricDiamondCurveNaturalityData
import Definitions.Def_MazurTransfer_Order13ActualDiamondGenericCurveOrder

noncomputable section
namespace MazurTransfer.Order13RationalGenericCurveLiftCompatibility
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem fieldLift_rational_eq (σ : actualCurveFunctionField ℚ ≃ₐ[ℚ] actualCurveFunctionField ℚ) :
    Order13FieldCurveAutomorphismLift.fieldLift ℚ σ =
      Order13ActualCurveFieldAutomorphismLift.fieldLift σ := by
  apply Iso.ext
  apply Order13ActualCurveFieldAutomorphismLift.hom_ext
    (Order13FieldCurveAutomorphismLift.fieldLift_over ℚ σ)
    (Order13ActualCurveFieldAutomorphismLift.fieldLift_over σ)
  exact (Order13FieldCurveAutomorphismLift.fieldLift_generic ℚ σ).trans
    (Order13ActualCurveFieldAutomorphismLift.fieldLift_generic σ).symm

theorem diamondAlgEquiv_rational_eq :
    Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv ℚ =
      Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv := by
  ext b
  exact RingHom.congr_fun Order13GeometricDiamondCurveNaturality.diamondRational_agrees b

theorem genericDiamondCurveIso_rational_eq :
    Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso ℚ =
      Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso := by
  unfold Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso
    Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso
  rw [diamondAlgEquiv_rational_eq]
  exact fieldLift_rational_eq _

variable (K : Type) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩

theorem existingDiamondCurve_baseChange :
    (Order13FieldDiamondGenericCurveOrder.genericDiamondCurveIso K).hom ≫
      Order13ActualCurveBaseChange.curveMap ℚ K =
    Order13ActualCurveBaseChange.curveMap ℚ K ≫
      Order13ActualDiamondGenericCurveOrder.genericDiamondCurveIso.hom := by
  rw [← genericDiamondCurveIso_rational_eq]
  exact Order13GeometricDiamondCurveNaturality.diamondCurve_baseChange K

end MazurTransfer.Order13RationalGenericCurveLiftCompatibility
#print axioms MazurTransfer.Order13RationalGenericCurveLiftCompatibility.existingDiamondCurve_baseChange


