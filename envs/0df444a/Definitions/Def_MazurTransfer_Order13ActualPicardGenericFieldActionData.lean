-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGenericFieldActionData
-- name    : MazurTransfer_Order13ActualPicardGenericFieldActionData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T15:28:31.446816+00:00
-- url     : https://prove2.me/theorems/4186c224-4ab7-41d6-842c-909daeb031dd
-- title:
--   Actual represented Picard inverse-pullback actions for rational function-field automorphisms
-- statement:
--   The original actualFieldAction and actualFieldHom assign genuine inverse-pullback represented Picard scheme automorphisms to arbitrary automorphisms of the actual rational curve function field. The original inverse-over-base, isomorphism, multiplication and identity certificates are retained, with their original complete types. Downstream consumers are arithmetic action compatibility and scheme norm descent.
-- source:
--   Unchanged original constructors and certificates from MazurTheorem Order13ActualPicardGenericFieldAction and inverse_over from Order13ActualPicardArithmeticPullbackNaturality. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2; Apache-2.0. Six original types and two data values compared, including both original rational algebra instances.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original generic field-action constructors and group-law certificates retained.
Design boundary: each actual rational function-field automorphism acts by a
genuine inverse-pullback automorphism of the actual represented Picard scheme,
respecting its group law on every test scheme.
Named downstream consumers: actualFieldHom_arithmetic and scheme norm descent.
Official Anthropic FLT Picard interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ActualDiamondGenericCurveOrder
import Definitions.Def_MazurTransfer_Order13ActualPicardDiamondSchemeEndomorphism
import Theorems.Thm_MazurTransfer_picard_pullback_isIso_of_curve_iso
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualCurveFieldAutomorphismLift MazurTransfer.Order13ActualDiamondGenericCurveOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ
namespace MazurTransfer.Order13ActualPicardArithmeticPullbackNaturality
theorem inverse_over (σ : F ≃ₐ[ℚ] F) :
    (fieldLift σ).inv ≫ curveToBase ℚ = curveToBase ℚ := by
  have h := fieldLift_over σ⁻¹
  rw [fieldLift_inv] at h
  exact h

end MazurTransfer.Order13ActualPicardArithmeticPullbackNaturality
namespace MazurTransfer.Order13ActualPicardGenericFieldAction
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualCurveFieldAutomorphismLift Order13ActualDiamondGenericCurveOrder
open Order13ActualPicardArithmeticPullbackNaturality Order13ActualPicardDiamondSchemeEndomorphism
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open PicardReRigidifiedCurvePullback
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra ℚ F := actualCurveFunctionFieldAlgebra ℚ

def actualFieldAction (σ : F ≃ₐ[ℚ] F) :
    PullbackData actualRepresentation (fieldLift σ).inv (inverse_over σ) :=
  (nonempty_pullbackData actualRepresentation (fieldLift σ).inv (inverse_over σ)).some

def actualFieldHom (σ : F ≃ₐ[ℚ] F) : SchemeHomOver actualPicard.toBase actualPicard.toBase :=
  (actualFieldAction σ).hom

theorem actualFieldHom_isIso (σ : F ≃ₐ[ℚ] F) : IsIso (actualFieldHom σ).1 :=
  MazurTransfer.picard_pullback_isIso_of_curve_iso actualRepresentation
    (fieldLift σ) (fieldLift_over σ) (inverse_over σ)
    (actualFieldHom σ) (actualFieldAction σ).classifies

theorem actualFieldHom_mul (σ : F ≃ₐ[ℚ] F) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) (a b : SchemeHomOver t actualPicard.toBase) :
    postComp (actualFieldHom σ) (actualLaw.mul t a b) =
      actualLaw.mul t (postComp (actualFieldHom σ) a) (postComp (actualFieldHom σ) b) :=
  (actualFieldAction σ).mul t a b

theorem actualFieldHom_one (σ : F ≃ₐ[ℚ] F) {T : Scheme}
    (t : T ⟶ Spec (CommRingCat.of ℚ)) :
    postComp (actualFieldHom σ) (actualLaw.one t) = actualLaw.one t :=
  (actualFieldAction σ).one t

end MazurTransfer.Order13ActualPicardGenericFieldAction

#print axioms MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldAction
#print axioms MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_isIso
#print axioms MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_mul
#print axioms MazurTransfer.Order13ActualPicardGenericFieldAction.actualFieldHom_one


