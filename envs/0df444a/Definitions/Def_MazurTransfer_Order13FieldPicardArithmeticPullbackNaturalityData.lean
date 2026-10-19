-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldPicardArithmeticPullbackNaturalityData
-- name    : MazurTransfer_Order13FieldPicardArithmeticPullbackNaturalityData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:43:24.085503+00:00
-- url     : https://prove2.me/theorems/ac980831-6ab1-4149-8bf4-cfe7549ea2c3
-- title:
--   Actual inverse-curve Picard pullback agrees with the field action on arithmetic classes over perfect characteristic-zero fields
-- statement:
--   The chosen inverse curve lift is over the base, and genuine re-rigidified pullback on a represented relative degree-zero Picard scheme induces the specified actual function-field automorphism on arithmetic Pic0 classes, over every perfect characteristic-zero field. Both complete original types, including the representation, pullback-data and point hypotheses, and the original local scalar algebra provider are compared. Named downstream consumer: geometric Picard diamond line-bundle and arithmetic-class compatibility.
-- source:
--   Complete original MazurTheorem Order13FieldPicardArithmeticPullbackNaturality using the accepted full degree-zero point presentation, arithmetic-class independence and base-field line-bundle pullback theorem. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: genuine re-rigidified inverse-curve pullback on represented
Picard schemes over every perfect characteristic-zero field induces the actual field-automorphism action on
arithmetic Pic0. Named downstream consumer: the generic-compatible diamond
Picard scheme action and its cyclotomic/norm identities.
-/
import Definitions.Def_MazurTransfer_Order13FieldCurveDivisorPresentationPullbackData
import Theorems.Thm_MazurTransfer_PicardCurvePullbackBaseFieldLineBundle_pointLineBundle_postComp_iso_pullback
import Definitions.Def_MazurTransfer_PicardReRigidifiedCurvePullbackData
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardPointMapData
import Theorems.Thm_MazurTransfer_order13_actual_picard_point_degreeZero_divisor_presentation
import Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation

noncomputable section
universe u
namespace MazurTransfer.Order13FieldPicardArithmeticPullbackNaturality
open CategoryTheory AlgebraicGeometry AlgebraicCurve AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13FieldCurveAutomorphismLift Order13FieldDiamondGenericCurveOrder
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open PicardReRigidifiedCurvePullback LineBundleFieldComparison Order13ArithmeticPicardPointMap
variable (K : Type u) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local notation "C" => curveScheme K
local notation "F" => actualCurveFunctionField K
local instance : Algebra K F := actualCurveFunctionFieldAlgebra K

theorem inverse_over (σ : F ≃ₐ[K] F) :
    (fieldLift K σ).inv ≫ curveToBase K = curveToBase K := by
  have h := fieldLift_over K σ⁻¹
  rw [fieldLift_inv K] at h
  exact h

theorem arithmeticClass_postComp_pullback
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (σ : F ≃ₐ[K] F)
    (N : PullbackData h (fieldLift K σ).inv (inverse_over K σ))
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :
    arithmeticClass K 𝒱 ε D h (postComp N.hom a) =
      σ • arithmeticClass K 𝒱 ε D h a := by
  obtain ⟨E, φ, hE⟩ := order13_actual_picard_point_degreeZero_divisor_presentation K 𝒱 ε D h a
  have hEa := arithmeticClass_eq_of_presentation K 𝒱 ε D h a E φ hE
  obtain ⟨ψ, hψ⟩ := Order13FieldCurveDivisorPresentationPullback.presentation_pullback K σ
    (pointLineBundle (curveToBase K) ε D h a) E.1 φ hE
  obtain ⟨e⟩ := PicardCurvePullbackBaseFieldLineBundle.pointLineBundle_postComp_iso_pullback
    (curveToBase K) ε D h (fieldLift K σ).inv (inverse_over K σ) N a
  have htarget := IsPresentation.of_iso e hψ
  have hNb := arithmeticClass_eq_of_presentation K 𝒱 ε D h (postComp N.hom a)
    (Pic0.degZeroSMulHom σ E) _ htarget
  calc
    arithmeticClass K 𝒱 ε D h (postComp N.hom a) = Pic0.mk (Pic0.degZeroSMulHom σ E) := hNb.symm
    _ = σ • Pic0.mk E := (Pic0.smul_mk σ E).symm
    _ = σ • arithmeticClass K 𝒱 ε D h a := congrArg (fun x => σ • x) hEa

end MazurTransfer.Order13FieldPicardArithmeticPullbackNaturality
#print axioms MazurTransfer.Order13FieldPicardArithmeticPullbackNaturality.arithmeticClass_postComp_pullback


