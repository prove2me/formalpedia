-- Prove2me | Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondPresentationData
-- name    : MazurTransfer_Order13ActualPicardGeometricDiamondPresentationData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:49:52.939976+00:00
-- url     : https://prove2.me/theorems/6ddff19e-720a-4b64-84a1-c7be059807c9
-- title:
--   Full divisor presentations of the actual geometric Picard point transform by the literal field diamond
-- statement:
--   Let K be a perfect characteristic-zero field and let a be a K-valued point of the existing rational represented Picard family. Every full divisor presentation of its actual line bundle transports, under the existing rational diamond Picard morphism, to a full presentation with divisor transformed by the literal diamond automorphism of the actual function field over K. The complete original type retains every point, section-map and presentation hypothesis. Named downstream consumer: arithmetic classes and scheme norm transport for the same Picard family.
-- source:
--   Complete original MazurTheorem Order13ActualPicardGeometricDiamondPresentation proof, using genuine geometric line-bundle pullback and full divisor-presentation pullback. Official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a supplied full divisor presentation of a geometric
Picard point transforms under the existing rational diamond by the actual
extension-field diamond. Named downstream consumer: identifying geometric
Picard arithmetic classes once degree-zero presentations are constructed.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardGeometricDiamondLineBundleData
import Definitions.Def_MazurTransfer_Order13FieldCurveDivisorPresentationPullbackData

noncomputable section
namespace MazurTransfer.Order13ActualPicardGeometricDiamondPresentation
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open Order13ActualPicardDiamondSchemeEndomorphism Order13ActualPicardGenericFieldAction
open Order13ActualPicardGeometricDiamondLineBundle
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
variable (K : Type) [Field K] [CharZero K] [PerfectField K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K
local instance : Algebra ℚ (actualCurveFunctionField ℚ) := actualCurveFunctionFieldAlgebra ℚ

theorem presentation_actualGenericDiamondHom
    (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) actualPicard.toBase)
    (D : Divisor K (actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens, Γ(actualGeometricPointLineBundle K a, U) →+ actualCurveFunctionField K)
    (h : IsPresentation (curveToBase K) (actualGeometricPointLineBundle K a) D φ) :
    ∃ ψ : ∀ U : (curveScheme K).Opens,
        Γ(actualGeometricPointLineBundle K
          (postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a), U) →+
          actualCurveFunctionField K,
      IsPresentation (curveToBase K)
        (actualGeometricPointLineBundle K
          (postComp (actualFieldHom Order13ActualDiamondFunctionFieldAutomorphism.diamondAlgEquiv) a))
        ((Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K) • D) ψ := by
  obtain ⟨ψ, hψ⟩ := Order13FieldCurveDivisorPresentationPullback.presentation_pullback K
    (Order13FieldDiamondFunctionFieldAutomorphism.diamondAlgEquiv K)
    (actualGeometricPointLineBundle K a) D φ h
  obtain ⟨e⟩ := actualGenericDiamondHom_geometric_point_pullback K a
  exact ⟨_, IsPresentation.of_iso e hψ⟩

end MazurTransfer.Order13ActualPicardGeometricDiamondPresentation
#print axioms MazurTransfer.Order13ActualPicardGeometricDiamondPresentation.presentation_actualGenericDiamondHom


