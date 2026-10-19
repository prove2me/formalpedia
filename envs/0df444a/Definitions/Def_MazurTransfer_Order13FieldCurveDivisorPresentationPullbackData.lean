-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldCurveDivisorPresentationPullbackData
-- name    : MazurTransfer_Order13FieldCurveDivisorPresentationPullbackData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:37:33.37113+00:00
-- url     : https://prove2.me/theorems/823a39a4-65d3-4046-8a7e-d330abb12eb8
-- title:
--   Inverse curve pullback transports full divisor presentations over characteristic-zero fields
-- statement:
--   For the original actual field curve over every characteristic-zero field, inverse pullback by the chosen generic-compatible lift transports any full line-bundle divisor presentation to the divisor acted on by the specified field automorphism. The complete original theorem type and original local scalar algebra provider are compared. Named downstream consumer: represented Picard arithmetic pullback naturality.
-- source:
--   Complete original MazurTheorem field divisor/relative Picard line-bundle transport contracts, constructors and proofs, including the full original invertible-sheaf field-rigidification helper where used. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inverse-curve pullback on the literal curve over every characteristic-zero field takes
any full divisor presentation to the divisor transported by the specified
actual field automorphism. Named downstream consumer: identification of
the genuine represented Picard action with arithmetic Pic0 transport.
-/
import Theorems.Thm_MazurTransfer_CurveIsoDivisorPresentationFieldAction_presentation_pullback
import Definitions.Def_MazurTransfer_Order13FieldCurveInversePlaceSetData

noncomputable section
universe u
namespace MazurTransfer.Order13FieldCurveDivisorPresentationPullback
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13FieldCurveAutomorphismLift Order13FieldDiamondGenericCurveOrder
open Order13FieldCurveInversePlaceSet
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type u) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local notation "C" => curveScheme K
local notation "F" => actualCurveFunctionField K
local instance : Algebra K F := actualCurveFunctionFieldAlgebra K

theorem presentation_pullback (σ : F ≃ₐ[K] F) (L : (curveScheme K).Modules) (D : Divisor K F)
    (φ : ∀ U : (curveScheme K).Opens, Γ(L, U) →+ F) (h : IsPresentation (curveToBase K) L D φ) :
    ∃ ψ : ∀ U : (curveScheme K).Opens, Γ((Scheme.Modules.pullback (fieldLift K σ).inv).obj L, U) →+ F,
      IsPresentation (curveToBase K) ((Scheme.Modules.pullback (fieldLift K σ).inv).obj L)
        (σ • D) ψ :=
  MazurTransfer.CurveIsoDivisorPresentationFieldAction.presentation_pullback
    (curveToBase K) (fieldLift K σ) σ L D φ h
    (fieldLift_inv_generic K σ) (inverse_placesOf K σ)

end MazurTransfer.Order13FieldCurveDivisorPresentationPullback
#print axioms MazurTransfer.Order13FieldCurveDivisorPresentationPullback.presentation_pullback


