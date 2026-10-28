-- Prove2me | Definitions.Def_OAIQ068A043
-- name    : OAIQ068A043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:29:05.300288+00:00
-- url     : https://prove2.me/theorems/96af837e-e995-425c-a035-cf8a5974bccb
-- title:
--   Definitions bundle OAIQ068A043 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 38 declarations of OpenAI's Lean: 6 definitions, 2 instances and 30 theorems. The definitions and types are `OAI.PiExponent.CurvePlaceCenter.centerMorphism`, `OAI.PiExponent.ExceptionalCurveDegree.idealDivisor`, `OAI.PiExponent.NumericalAmpleness.CartierEulerPair.leftComplex`, `OAI.PiExponent.NumericalAmpleness.CartierEulerPair.middleIso`, `OAI.PiExponent.NumericalAmpleness.CartierEulerPair.rightComplex`, `OAI.PiExponent.NumericalAmpleness.lineEuler`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Cohomology_CartierEulerPair`, `PiExponent_Cohomology_MixedEulerDimension`, `PiExponent_Geometry_CurveGlobalCoordinateOrder`, `PiExponent_Geometry_CurveGlobalMonomialLocal`, `PiExponent_Geometry_CurveNormalizationProjective`, `PiExponent_Geometry_CurveNormalizedDegreeTransfer`, `PiExponent_Geometry_CurvePlaceCenter`, `PiExponent_Geometry_CurvePlaceCenterStalk`, `PiExponent_Geometry_CurvePlaceSectionDivisor`, `PiExponent_Geometry_CurvePlaceSectionOrder`, `PiExponent_Geometry_WeightedProjectiveCurveDegree`, `PiExponent_Polynomials_WeightedMonomialFamilyLattice`.
--
--   **Imports.** It imports the bundles `OAIQ068A040`, `OAIQ068A041` and `OAIQ068A042` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A046`; the statements `OAI_PiExponent_NumericalAmpleness_mixedDifference_lineEuler_of_ample`, `OAI.PiExponent.NumericalAmpleness.mixedDifference_lineEuler_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_cartier_restriction`, `OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_curve_margin`, `OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_power_cartier_restriction` and `OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68`; the proofs of `OAI_PiExponent_AdmissibleJetSurjectivity_blowupBundle_ample`, `OAI.PiExponent.AdmissibleJetSurjectivity.blowupBundle_ample_q68`, `OAI_PiExponent_NumericalAmpleness_exists_power_section_cover_of_euler_growth`, `OAI.PiExponent.NumericalAmpleness.exists_power_section_cover_of_euler_growth_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_cartier_restriction`, `OAI.PiExponent.NumericalAmpleness.mixedTop_cartier_restriction_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_curve_margin`, `OAI.PiExponent.NumericalAmpleness.mixedTop_curve_margin_q68`, `OAI_PiExponent_NumericalAmpleness_mixedTop_power_cartier_restriction` and `OAI.PiExponent.NumericalAmpleness.mixedTop_power_cartier_restriction_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041
import Definitions.Def_OAIQ068A042

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceSectionDivisor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter

namespace PiExponent.CurvePlaceSectionDivisor


variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem degree_eq_euler_difference (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf (parameterCurve f hf)) n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology (structureSheaf (parameterCurve f hf)) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology L.sheaf n)) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) := by
  let : Subsingleton (cohomology (structureSheaf (parameterCurve f hf)) 2) := by
    apply subsingleton_of_forall_eq 0
    intro x
    exact parameterCurve_lineBundle_ext_zero f hf (L.pow 0) 2 (by omega) x
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp)]
  exact SectionOrderDivisor.divisor_degree_eq_euler_difference
    (parameterCurveStructureMap f hf) (parameterCurve_dimension_le_one f hf)
    (parameterCurve_stalkDVR f hf) L s hs hfiniteO hfiniteL

theorem degree_eq_euler_difference_full (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) :=
  degree_eq_euler_difference f hf L s hs
    (parameterCurve_finiteLineCohomology f hf (L.pow 0))
    (parameterCurve_finiteLineCohomology f hf L)

end PiExponent.CurvePlaceSectionDivisor

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceCenter
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurvePlaceCenter
open AlgebraicGeometry CategoryTheory
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces

def centerMorphism
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f hf p.valuation p.constants_nonneg hp)) ≫
      zeroChartInclusion f hf
  else
    Spec.map (CommRingCat.ofHom (parameterChartValuationHom f⁻¹ (transcendental_inverse f hf)
      p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le)) ≫
      infinityChartInclusion f hf

theorem centerMorphism_closedPoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
      placePoint f hf p := by
  by_cases hp : 0 ≤ p.valuation f
  · simp only [centerMorphism, placePoint, dite_eq_left hp]
    rfl
  · simp only [centerMorphism, placePoint, dite_eq_right hp]
    rfl

theorem centerMorphism_generic_of_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  rw [centerMorphism, dite_eq_left hp, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_zeroChart]
  rfl

theorem centerMorphism_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) :
    Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫
      centerMorphism f hf p = parameterCurveGenericPoint f hf := by
  by_cases hp : 0 ≤ p.valuation f
  · exact centerMorphism_generic_of_regular f hf p hp
  · rw [centerMorphism, dite_eq_right hp, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, parameterCurveGenericPoint_eq_infinityChart]
    rfl

theorem centerMorphism_comp_eq_of_generic
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) {Y : Scheme.{u}} [Y.IsSeparated]
    (g : parameterCurve f hf ⟶ Y)
    (φ : Spec (CommRingCat.of (PlaceValuationRing.ring p)) ⟶ Y)
    (hφ : Spec.map (CommRingCat.ofHom (algebraMap (PlaceValuationRing.ring p) E)) ≫ φ =
      parameterCurveGenericPoint f hf ≫ g) : centerMorphism f hf p ≫ g = φ := by
  apply hom_ext_fraction (PlaceValuationRing.ring p) E
  rw [← Category.assoc, centerMorphism_generic]
  exact hφ.symm

end PiExponent.CurvePlaceCenter

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceCenterStalk
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurvePlaceCenter
open CategoryTheory AlgebraicGeometry
open CurveZeroPole CurveValuationCenter CurveNormalizationModel CurveModelPlaces
universe u
variable {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]
variable (p : NormalizedPlace F E)

instance centerMorphism_stalkMap_isIso :
    IsIso ((centerMorphism f hf p).stalkMap (IsLocalRing.closedPoint (PlaceValuationRing.ring p))) := by
  have hx : centerMorphism f hf p (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  let := parameterCurve_stalkDVR f hf _ hx
  exact BirationalValuationStalk.stalkMap_isIso (centerMorphism f hf p)
    (parameterCurveFunctionFieldEquiv f hf) (centerMorphism_generic f hf p)

instance centerMorphism_stalkClosedPointTo_isIso :
    IsIso (Scheme.stalkClosedPointTo (centerMorphism f hf p)) := by
  unfold Scheme.stalkClosedPointTo
  infer_instance

end PiExponent.CurvePlaceCenter

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceSectionOrder
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder

namespace PiExponent.CurvePlaceSectionOrder


variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_local_order (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E)
    (e : (Scheme.Modules.pullback (centerMorphism f hf p)).obj L.sheaf ≅
      O (Spec (CommRingCat.of (PlaceValuationRing.ring p)))) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat := by
  let : IsDiscreteValuationRing ((parameterCurve f hf).presheaf.stalk
      ((centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)))) := by
    rw [centerMorphism_closedPoint]
    exact parameterCurve_stalkDVR f hf _ (placePoint_ne_genericPoint f hf p)
  have h := LocalPullbackSectionOrder.sectionOrder_eq_germ_order
    (centerMorphism f hf p) L s e
  have hp : (centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ≠
      genericPoint (parameterCurve f hf) := by
    rw [centerMorphism_closedPoint]
    exact placePoint_ne_genericPoint f hf p
  have h' : (sectionOrder e (pullbackSection (centerMorphism f hf p) s)).toNat =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :=
    congrArg ENat.toNat h
  have heq : (⟨(centerMorphism f hf p) (IsLocalRing.closedPoint (PlaceValuationRing.ring p)), hp⟩ :
      SectionOrderDivisor.CurvePoint (parameterCurve f hf)) =
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
    apply Subtype.ext
    exact centerMorphism_closedPoint f hf p
  rw [heq] at h'
  exact (CurvePlaceSectionDivisor.divisor_apply f hf L s hs p).trans h'.symm

end PiExponent.CurvePlaceSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem inverseSection_zeroIdeal (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    [J.sheaf.IsQuasicoherent] :
    zeroIdeal J.inverse (inverseSection J ι) = imageIdealSheaf ι := by
  classical
  have hc (y : Y) := common_affine_frames J J.inverse y
  choose U hy e f using hc
  let e' y := (e y).some
  let f' y := (f y).some
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    let b := tensorFrame J J.inverse V.1 (e' y) (f' y)
    rw [zeroIdeal_on_frame J.inverse (inverseSection J ι) V (f' y),
      imageIdealSheaf_on_frame ι V (e' y)]
    change Ideal.span {affineMapCoefficient V a (f' y)
      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι)} = _
    erw [affineMapCoefficient_comp V a b (f' y),
      ← Ideal.span_singleton_mul_span_singleton]
    have hu : IsUnit (affineMapCoefficient V a b (lineTensorInverseIso J).inv) := by
      apply IsUnit.map V.1.topIso.hom.hom
      exact (end_isIso_iff _).mp
        (a.symm ≪≫ ((Scheme.Modules.restrictFunctor V.1.ι).mapIso
          (lineTensorInverseIso J)).symm ≪≫ b).isIso_hom
    rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul]
    exact tensor_inclusion_ideal J J.inverse ι V (e' y) (f' y)

theorem inverseSection_zeroIdeal_eq_comap
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) :
    zeroIdeal J.inverse (inverseSection J ι) = I.comap π := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  rw [inverseSection_zeroIdeal, PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]

theorem zeroIdeal_pullback (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (f : Y ⟶ X) :
    zeroIdeal (L.pullback f) (pullbackSection f s) = (zeroIdeal L s).comap f := by
  classical
  have hlocal (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (zeroIdeal (L.pullback f) (pullbackSection f s)).ideal V =
        ((zeroIdeal L s).comap f).ideal V := by
    obtain ⟨U, hU, ⟨e⟩⟩ := PiExponentSeshadri.InvertibleLocal.affine_frame L (f y)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ U.1 from hU)
    let g := f.resLE U.1 V hVU
    obtain ⟨eF, he⟩ := exists_restricted_pullback_frame_all_of_factor f U.1 V g
      (Scheme.Hom.resLE_comp_ι f hVU).symm e
    refine ⟨⟨V, hV⟩, hyV, ?_⟩
    rw [zeroIdeal_on_frame (L.pullback f) (pullbackSection f s) ⟨V, hV⟩ eF,
      PiExponentSeshadri.IdealPullback.comap_ideal (zeroIdeal L s) f ⟨V, hV⟩ U hVU,
      zeroIdeal_on_frame L s U e, Ideal.map_span, Set.image_singleton]
    erw [he s]
    congr 2
    change V.topIso.hom ((f.resLE U.1 V hVU).appTop _) = _
    have ht : (f.resLE U.1 V hVU).appTop = U.1.topIso.hom ≫
        f.appLE U.1 V hVU ≫ V.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using!
        (Scheme.Hom.resLE_app_top f hVU)
    rw [ht]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  choose V hy hV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · exact hV

theorem zeroIdeal_zero (L : LineBundle X) : zeroIdeal L 0 = ⊥ := by
  classical
  choose U hx e using fun x : X => PiExponentSeshadri.InvertibleLocal.affine_frame L x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    rw [zeroIdeal_on_frame L 0 (U x) (e x).some]
    erw [restrictSection_zero, coefficient_zero, map_zero, Ideal.span_singleton_zero]
    rfl

theorem pullback_inverseSection_zeroIdeal
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) :
    zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)) =
      I.comap (g ≫ π) := by
  rw [zeroIdeal_pullback, inverseSection_zeroIdeal_eq_comap I π J ι hJ,
    Scheme.IdealSheafData.comap_comp]

theorem pullback_inverseSection_ne_zero
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥) :
    pullbackSection g (inverseSection J ι) ≠ 0 := by
  intro hs
  have h := pullback_inverseSection_zeroIdeal I π J ι hJ g
  rw [hs] at h
  exact hg (h.symm.trans (zeroIdeal_zero _))

theorem zeroIdeal_spec_top {A : Type} [CommRing A]
    (L : LineBundle (Spec (CommRingCat.of A)))
    (s : GlobalSections _ L.sheaf) (e : L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    ((zeroIdeal L s).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
        Ideal.span {LocalSectionOrder.localCoefficient e s} := by
  change (imageIdeal (L.dualSection s) ⊤).map _ = _
  rw [imageIdeal_top_of_frame (L.dualSection s)
    (InverseFrames.pairingFrame (lineTensorInverseIso L) e)]
  change (Ideal.span {endValue ((InverseFrames.pairingFrame (lineTensorInverseIso L) e).inv ≫
    InverseFrames.dualMap (lineTensorInverseIso L) s)}).map _ = _
  erw [InverseFrames.dualMap_coefficient]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem compactIdeal_comap_ne_bot_of_generic {m : ℕ} {K : Type} [Fintype K]
    (c : K → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (CompactLogJetIdeal.compactIdeal c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold CompactLogJetIdeal.polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : K, (CompactJetPolynomial.powerIdeal (c k)
        (CompactJetPolynomial.logPolynomials T) e).map (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => map_powerIdeal_eq_top_of_transcendental z hz (c k) T e
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    {m : ℕ} (j : CompactLogJetIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (Fin.cases 1 c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (Fin.cases 1 c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (Fin.cases 1 c) hc P

theorem divisor_eq_localIdeal_length
    (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections _ L.sheaf) (hs : s ≠ 0) (p : NormalizedPlace ℂ E) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸ localIdeal (zeroIdeal L s) (centerMorphism f hf p))).toNat := by
  let q := centerMorphism f hf p
  obtain ⟨e, he⟩ := LocalPullbackSectionOrder.exists_frame_coefficient_germ q L
  have hn : localCoefficient e (pullbackSection q s) ≠ 0 := by
    rw [he s]
    apply (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo q)).injective).mpr
    exact SectionZeroStalk.sectionGerm_ne_zero L s hs
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).openSet
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).frame _
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).mem
  have hi : localIdeal (zeroIdeal L s) q =
      Ideal.span {localCoefficient e (pullbackSection q s)} := by
    unfold localIdeal
    rw [← zeroIdeal_pullback L s q]
    exact zeroIdeal_spec_top (L.pullback q) (pullbackSection q s) e
  rw [CurvePlaceSectionOrder.divisor_eq_local_order f hf L s hs p e, hi,
    CurveLocalOrder.length_quotient_span_eq_addVal hn]
  rfl

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

def idealDivisor : NormalizedPlace ℂ E →₀ ℕ :=
  CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)

theorem idealDivisor_apply (p : NormalizedPlace ℂ E) :
    idealDivisor f hf I π J ι hJ g hg p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸
          localIdeal I (centerMorphism f hf p ≫ g ≫ π))).toNat := by
  erw [idealDivisor, divisor_eq_localIdeal_length]
  have hi : localIdeal
      (zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)))
        (centerMorphism f hf p) = localIdeal I (centerMorphism f hf p ≫ g ≫ π) := by
    simp only [localIdeal, pullback_inverseSection_zeroIdeal I π J ι hJ g,
      Scheme.IdealSheafData.comap_comp]
  rw [hi]

theorem degree_eq_neg_idealDivisor_sum :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(idealDivisor f hf I π J ι hJ g hg).sum (fun _ n => (n : ℤ)) := by
  have hd := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf
    (J.inverse.pullback g) (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)
  have ht := parameterCurve_tensor_euler_add f hf (J.pullback g) (J.inverse.pullback g)
  let e : ((J.pullback g).tensor (J.inverse.pullback g)).sheaf ≅
      structureSheaf (parameterCurve f hf) :=
    (PiExponentSeshadri.PullbackTensor.iso g J J.inverse).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (lineTensorInverseIso J) ≪≫ pullbackUnitIso g
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf) e 1
  change _ = -(CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι)) _).sum (fun _ n => (n : ℤ))
  omega

end Curve

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerPair
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

namespace CartierEulerPair

def middleIso (L B M : LineBundle X) (n : ℕ) :
    (middle L B M n).sheaf ≅ (B.tensor (source L M (n+1))).sheaf :=
  moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl (source L M n).sheaf) ≪≫
    lineTensorAssoc B L (source L M n) ≪≫
    moduleTensorIso (Iso.refl B.sheaf) (lineTensorAssoc L (L.pow n) M).symm

def leftComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (s : GlobalSections X (L.tensor B).sheaf) [Mono s] (n : ℕ) : ShortComplex X.Modules :=
  tensorSectionComplex p (L.tensor B) (source L M n) s

def rightComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (L B M : LineBundle X)
    (t : GlobalSections X B.sheaf) [Mono t] (n : ℕ) : ShortComplex X.Modules :=
  let T := tensorSectionComplex p B (source L M (n+1)) t
  ShortComplex.mk (T.f ≫ (middleIso L B M n).inv)
    ((middleIso L B M n).hom ≫ T.g) (by
      exact (Category.assoc T.f (middleIso L B M n).inv
        ((middleIso L B M n).hom ≫ T.g)).trans
        ((congrArg (fun q => T.f ≫ q) ((middleIso L B M n).inv_hom_id_assoc T.g)).trans
          T.zero))

end CartierEulerPair
end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.SectionZeroIdeal PiExponent.ProjectiveO1

def lineEuler {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ)) (r : ℕ)
    (M : LineBundle X) : ℤ := eulerCharacteristic p r M.sheaf

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalMonomialLocal
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CurveGlobalMonomialLocal
open AlgebraicGeometry CategoryTheory MvPolynomial
open ProjectiveLatticePullback ProjectiveLocalCoefficients WeightedSectionOrder
open WeightedLocalLattice PiExponentSeshadri.Projective
open scoped BigOperators
attribute [local instance] MvPolynomial.gradedAlgebra

theorem centerMorphism_eq_latticeProjectiveMap
    {F E σ : Type} [Field F] [Field E] [Algebra F E] [Fintype σ]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (g : CurveNormalizationModel.parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace F σ)
    (y : σ → E) (z : σ) (hz : y z = 1)
    (hg : CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g =
      normalizedMap (algebraMap F E) y z hz)
    (p : CurveValuationCenter.NormalizedPlace F E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i}) :
    CurvePlaceCenter.centerMorphism f hf p ≫ g =
      latticeProjectiveMap (algebraMap F (PlaceValuationRing.ring p)) y i hi hspan := by
  apply CurvePlaceCenter.centerMorphism_comp_eq_of_generic f hf p
  rw [latticeProjectiveMap_generic _ y i hi hspan z hz, hg]
  rfl

end PiExponent.CurveGlobalMonomialLocal

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveGlobalCoordinateOrder
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter PiExponent.CurvePlaceCenter
open PiExponent.LocalSectionOrder PiExponent.WeightedLocalLattice
open PiExponent.ProjectiveLatticePullback PiExponent.WeightedPolynomialPole

namespace PiExponent.CurveGlobalCoordinateOrder


variable {E σ : Type} [Field E] [Algebra ℂ E] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
variable (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
variable (y : σ → E) (z : σ) (hz : y z = 1)
variable (hg : parameterCurveGenericPoint f hf ≫ g =
  ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E) y z hz)
include hg

omit [Fintype σ] in
theorem coordinateSection_ne_zero (b : σ) (hb : y b ≠ 0) :
    pullbackSection g (ProjectiveO1.coordinateSection b) ≠ 0 := by
  have hex : ∃ e : (Scheme.Modules.pullback (parameterCurveGenericPoint f hf ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅ O (Spec (CommRingCat.of E)),
      localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
        (ProjectiveO1.coordinateSection b)) = y b := by
    rw [hg]
    obtain ⟨e, he⟩ := ProjectiveLocalCoefficients.exists_frame_coordinate_coefficients
      (algebraMap ℂ E) y z hz
    exact ⟨e, he b⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (parameterCurveGenericPoint f hf) g e
  have heq := congrArg (fun c => (Scheme.ΓSpecIso (CommRingCat.of E)).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (parameterCurveGenericPoint f hf)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
    localCoefficient e (pullbackSection (parameterCurveGenericPoint f hf ≫ g)
      (ProjectiveO1.coordinateSection b)) at heq
  rw [he] at heq
  intro hs
  rw [hs] at heq
  have hz' : pullbackSection (parameterCurveGenericPoint f hf)
      (0 : O (parameterCurve f hf) ⟶
        (Scheme.Modules.pullback g).obj (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) = 0 := by
    simp [pullbackSection]
  rw [hz', (localCoefficient_eq_zero_iff _ _).mpr rfl] at heq
  exact hb heq.symm

theorem coordinate_divisor_order (p : NormalizedPlace ℂ E) (i : σ) (hi : y i ≠ 0)
    (hspan : generatedLattice (PlaceValuationRing.ring p) y Finset.univ =
      Submodule.span (PlaceValuationRing.ring p) {y i})
    (b : σ) (hb : y b ≠ 0) :
    (CurvePlaceSectionDivisor.divisor f hf
      ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g)
      (pullbackSection g (ProjectiveO1.coordinateSection b))
      (coordinateSection_ne_zero f hf g y z hz hg b hb) p : ℤ) =
      coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
  have hmap := CurveGlobalMonomialLocal.centerMorphism_eq_latticeProjectiveMap
    f hf g y z hz hg p i hi hspan
  have hex : ∃ e : (Scheme.Modules.pullback (centerMorphism f hf p ≫ g)).obj
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf ≅
        O (Spec (CommRingCat.of (PlaceValuationRing.ring p))),
      ((sectionOrder e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b))).toNat : ℤ) =
        coordinateOrder p.valuation (y b) - coordinateOrder p.valuation (y i) := by
    rw [hmap, PlaceValuationRing.valuation_eq_fractionAddValuation]
    obtain ⟨e, he⟩ := ProjectiveLatticeOrder.exists_frame_coordinate_orders
      (algebraMap ℂ (PlaceValuationRing.ring p)) y i hi hspan
    exact ⟨e, he b hb⟩
  obtain ⟨e, he⟩ := hex
  obtain ⟨e', he'⟩ := CompositePullbackCoefficient.exists_frame (centerMorphism f hf p) g e
  erw [CurvePlaceSectionOrder.divisor_eq_local_order f hf _ _ _ p e']
  have heq := congrArg
    (fun c => (Scheme.ΓSpecIso (CommRingCat.of (PlaceValuationRing.ring p))).hom c)
    (he' (ProjectiveO1.coordinateSection b))
  change localCoefficient e' (pullbackSection (centerMorphism f hf p)
    (pullbackSection g (ProjectiveO1.coordinateSection b))) =
      localCoefficient e (pullbackSection (centerMorphism f hf p ≫ g)
        (ProjectiveO1.coordinateSection b)) at heq
  unfold sectionOrder at he ⊢
  exact (congrArg (fun c : PlaceValuationRing.ring p =>
    ((IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p) c).toNat : ℤ)) heq).trans he

end PiExponent.CurveGlobalCoordinateOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationProjective
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open CurveNormalizationModel

variable {X : Scheme.{0}} [IsIntegral X]
variable {σ : Type} [Finite σ] [Nonempty σ]
variable {E : Type} [Field E] [Algebra ℂ E]

theorem parameterCurve_pullback_euler_degree
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (j : X ⟶ ProjectiveO1.projectiveSpace ℂ σ) [IsClosedImmersion j]
    (hj : j ≫ polynomialProjectiveProjection ℂ σ = p)
    (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  let : X.IsSeparated := by
    rw [Scheme.isSeparated_iff, ← terminal.comp_from p]
    infer_instance
  let : (structureSheaf X).IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  let : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf X)).choose.isQuasicoherent
  let : L.sheaf.IsFinitePresentation :=
    GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  obtain ⟨U,V,hU,hV,hcover⟩ :=
    ProjectiveCurveTwoAffine.two_affine_cover_of_closed_embedding j hd
  let : Subsingleton (cohomology (structureSheaf X) 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  let : Subsingleton (cohomology L.sheaf 2) :=
    CurveTwoAffineVanishing.cohomology_subsingleton U V hU hV hcover _ 2 le_rfl
  have hO : LowCohomologyFinite p (structureSheaf X) := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hL : LowCohomologyFinite p L.sheaf := fun n _ =>
    ProjectiveFiniteCoordinates.projectiveOver_cohomology_finite p j hj _ n
  have hOY : LowCohomologyFinite (g ≫ p) (structureSheaf (parameterCurve f hf)) := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf ((parameterCurvePolarization f hf).pow 0)
  have hLY : LowCohomologyFinite (g ≫ p) (L.pullback g).sheaf := by
    rw [hg]
    exact parameterCurve_finiteLineCohomology f hf (L.pullback g)
  simpa only [hg] using
    pullback_euler_degree_of_open_iso g p hd W hW U V hU hV hcover L hO hL hOY hLY

theorem parameterCurve_pullback_euler_degree_of_ample
    (p : X ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (hd : topologicalKrullDim X ≤ 1)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ X) [IsFinite g]
    (hg : g ≫ p = parameterCurveStructureMap f hf)
    (W : X.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle X) :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (L.pullback g).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  classical
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := ⟨⟩
  obtain ⟨n,hn,τ,hτ,s,hs,hclosed⟩ := H.ample_projective_sections_noetherian p hH
  let : Fintype τ := hτ
  have : Nonempty τ := by
    have hx : genericPoint X ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hs]
      trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  let j : X ⟶ ProjectiveO1.projectiveSpace ℂ τ := sectionsMorphism (baseScalars p) s hs
  have : IsClosedImmersion j := hclosed
  have hj : j ≫ polynomialProjectiveProjection ℂ τ = p := by
    rw [← AmpleCohomologyFinite.projectiveBase_eq_polynomialProjectiveProjection]
    exact (sectionsMorphism_over (baseScalars p) s hs).trans (toSpec_scalarMap p)
  exact parameterCurve_pullback_euler_degree p j hj hd f hf g hg W hW L

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialFamilyLattice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkClosedPointTo_isIso _root_.OAI.PiExponent.CurvePlaceCenter.centerMorphism_stalkMap_isIso _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open PiExponent.CurveValuationCenter PiExponent.WeightedPolynomialPole
open PiExponent.WeightedLocalLattice PiExponent.CurveGlobalMonomialLocal

namespace PiExponent.WeightedMonomialFamilyLattice

theorem exists_generator
    {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
    (p : NormalizedPlace ℂ E) (a : σ → ι →₀ ℕ) (x : ι → E)
    (z : σ) (hz : a z = 0) (w : ι → ℚ) (hw : ∀ j, 0 < w j)
    {R : ℚ} (hR : 0 < R) (powers : ι → ℕ)
    (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R) :
    ∃ i : σ, monomialCoordinates (F := ℂ) a x i ≠ 0 ∧
      (coordinateOrder p.valuation (monomialCoordinates (F := ℂ) a x i) : ℚ) =
        -R * coordinatePole p.valuation x w ∧
      generatedLattice (PlaceValuationRing.ring p) (monomialCoordinates (F := ℂ) a x)
        Finset.univ = Submodule.span (PlaceValuationRing.ring p)
          {monomialCoordinates (F := ℂ) a x i} := by
  classical
  let M : Finset (ι → ℕ) := Finset.univ.image (fun s : σ => fun j => a s j)
  have hzero : 0 ∈ M := by
    apply Finset.mem_image.mpr
    refine ⟨z, Finset.mem_univ z, ?_⟩
    funext j
    simp [hz]
  have hpureM : ∀ j, Pi.single j (powers j) ∈ M := by
    intro j
    apply Finset.mem_image.mpr
    refine ⟨pure j, Finset.mem_univ _, ?_⟩
    ext k
    simp [hpure, Finsupp.single_apply, Pi.single_apply, eq_comm]
  have hbudgetM : ∀ b ∈ M, (∑ j, w j * (b j : ℚ)) ≤ R := by
    intro b hb
    obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hb
    exact hbudget s
  obtain ⟨b, hb, hbn, hbo, hmin⟩ := WeightedMonomialPole.exists_minimizing_monomial
    p.valuation x w hw hR powers hpowers M hzero hpureM hbudgetM
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
  have hn : monomialCoordinates (F := ℂ) a x i ≠ 0 := by
    simpa only [monomialCoordinates_eq_prod] using hbn
  refine ⟨i, hn, ?_, ?_⟩
  · simpa only [monomialCoordinates_eq_prod] using hbo
  · apply generatedLattice_eq_span_of_minimum _ Finset.univ i (Finset.mem_univ i) hn
    intro j hj
    rw [← PlaceValuationRing.valuation_eq_fractionAddValuation]
    simpa only [monomialCoordinates_eq_prod] using
      hmin (fun k => a j k) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)

end PiExponent.WeightedMonomialFamilyLattice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedProjectiveCurveDegree
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CurveNormalizationModel PiExponent.CurveValuationCenter
open PiExponent.CurveGlobalMonomialLocal PiExponent.WeightedPolynomialPole
open PiExponent.CurveGlobalCoordinateOrder

namespace PiExponent.WeightedProjectiveCurveDegree


variable {E ι σ : Type} [Field E] [Algebra ℂ E] [Fintype ι] [Fintype σ]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem ambient_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (g : parameterCurve f hf ⟶ ProjectiveO1.projectiveSpace ℂ σ)
    (hg : parameterCurveGenericPoint f hf ≫ g =
      ProjectiveLocalCoefficients.normalizedMap (algebraMap ℂ E)
        (monomialCoordinates (F := ℂ) a x) z (monomialCoordinates_zero a x z hz))
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  classical
  let y := monomialCoordinates (F := ℂ) a x
  have hyz : y z = 1 := monomialCoordinates_zero a x z hz
  have hyzn : y z ≠ 0 := hyz ▸ one_ne_zero
  let L := (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).pullback g
  let s := pullbackSection g (ProjectiveO1.coordinateSection z)
  have hs : s ≠ 0 := coordinateSection_ne_zero f hf g y z hyz hg z hyzn
  let D := CurvePlaceSectionDivisor.divisor f hf L s hs
  let P := CurveContactSum.weightedPoleDivisor hfinite x w
  have hcoeff : ∀ p, (D p : ℝ) = (R : ℝ) * (P p : ℝ) := by
    intro p
    obtain ⟨i, hi, horder, hspan⟩ := WeightedMonomialFamilyLattice.exists_generator
      p a x z hz w hw hR powers hpowers pure hpure hbudget
    have hd := coordinate_divisor_order f hf g y z hyz hg p i hi hspan z hyzn
    have hzero : coordinateOrder p.valuation (y z) = 0 := by
      rw [hyz]
      simp [coordinateOrder]
    rw [hzero, zero_sub] at hd
    have hq : (D p : ℚ) = R * coordinatePole p.valuation x w := by
      have hdq : (D p : ℚ) = -(coordinateOrder p.valuation (y i) : ℚ) := by
        exact_mod_cast hd
      rw [hdq, horder]
      ring
    exact_mod_cast hq
  let T := D.support ∪ P.support
  have hDT : D.support ⊆ T := Finset.subset_union_left
  have hPT : P.support ⊆ T := Finset.subset_union_right
  have hdeg := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf L s hs
  change ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
    eulerCharacteristic (parameterCurveStructureMap f hf) 1
      (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) = _
  rw [← hdeg]
  change ((D.sum (fun _ n => (n : ℤ)) : ℤ) : ℝ) = (R : ℝ) * P.sum (fun _ n => (n : ℝ))
  rw [D.sum_of_support_subset hDT (fun _ n => (n : ℤ)) (by simp),
    P.sum_of_support_subset hPT (fun _ n => (n : ℝ)) (by simp)]
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun p _ => hcoeff p)

theorem weighted_pullback_degree
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (g : parameterCurve f hf ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) a))
    (hg : parameterCurveGenericPoint f hf ≫ g =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1
        ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g (WeightedCompactification.projectiveMonomialMap a)).app
      (ProjectiveO1.lineBundle (R := ℂ) (σ := σ)).sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
      ((WeightedCompactification.lineBundle (R := ℂ) a).pullback g).sheaf = _ at he
  rw [he]
  apply ambient_pullback_degree f hf a x z hz _ _ w hw hR powers hpowers pure hpure hbudget hfinite
  rw [← Category.assoc, hg]
  exact genericMonomialMap_comp_projectiveMonomialMap a z hz coordinate hcoordinate x

end PiExponent.WeightedProjectiveCurveDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizedDegreeTransfer
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizedDegreeTransfer
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness CurveNormalizationModel
variable {B X : Scheme.{0}} {E : Type} [Field E] [Algebra ℂ E]

theorem curveDegree_eq_normalized
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)] (L : LineBundle B) :
    curveDegree p L C =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (L.pullback (g ≫ C.embedding)).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) := by
  have h := CurveNormalizationDegree.parameterCurve_pullback_euler_degree_of_ample
    (C.embedding ≫ p) (H.pullback C.embedding)
    (LineBundle.IsAmple.pullback_closedImmersion H hH C.embedding)
    C.dimension.le f hf g hg W hW (L.pullback C.embedding)
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp g C.embedding).app L.sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((L.pullback C.embedding).pullback g).sheaf = _ at he
  rw [he] at h
  exact h.symm

theorem curveDegree_pullback_eq_normalized
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)]
    (π : B ⟶ X) (L : LineBundle X) :
    curveDegree p (L.pullback π) C =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (L.pullback (g ≫ C.embedding ≫ π)).sheaf -
        eulerCharacteristic (parameterCurveStructureMap f hf) 1
          (structureSheaf (parameterCurve f hf)) := by
  rw [curveDegree_eq_normalized p H hH C f hf g hg W hW]
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf)
    ((Scheme.Modules.pullbackComp (g ≫ C.embedding) π).app L.sheaf) 1
  change eulerCharacteristic (parameterCurveStructureMap f hf) 1
    ((L.pullback π).pullback (g ≫ C.embedding)).sheaf = _ at he
  rw [he]
  simp only [Category.assoc, LineBundle.pullback]

theorem weighted_curveDegree
    {ι σ : Type} [Fintype ι] [Fintype σ]
    (a : σ → ι →₀ ℕ) (x : ι → E) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ j, a (coordinate j) = Finsupp.single j 1)
    (p : B ⟶ Spec (.of ℂ)) [IsProper p]
    (H : LineBundle B) (hH : H.IsAmple) (C : IntegralCurve B)
    (f : E) (hf : Transcendental ℂ f)
    [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]
    (g : parameterCurve f hf ⟶ C.scheme) [IsFinite g]
    (hg : g ≫ C.embedding ≫ p = parameterCurveStructureMap f hf)
    (W : C.scheme.Opens) (hW : W ≠ ⊥) [IsIso (g ∣_ W)]
    (π : B ⟶ Proj (WeightedCompactification.imageGrade (R := ℂ) a))
    (hcoord : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ π) =
      CurveMonomialMap.genericMonomialMap a z hz coordinate hcoordinate x)
    (w : ι → ℚ) (hw : ∀ j, 0 < w j) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ j, w j * (powers j : ℚ) = R)
    (pure : ι → σ) (hpure : ∀ j, a (pure j) = Finsupp.single j (powers j))
    (hbudget : ∀ s, (∑ j, w j * (a s j : ℚ)) ≤ R)
    (hfinite : ∀ q : E, Transcendental ℂ q →
      FiniteDimensional (IntermediateField.adjoin ℂ {q}) E) :
    (curveDegree p ((WeightedCompactification.lineBundle (R := ℂ) a).pullback π) C : ℝ) =
      (R : ℝ) * CurveContactSum.weightedDegree hfinite x w := by
  rw [curveDegree_pullback_eq_normalized p H hH C f hf g hg W hW]
  exact WeightedProjectiveCurveDegree.weighted_pullback_degree f hf a x z hz
    coordinate hcoordinate (g ≫ C.embedding ≫ π) hcoord w hw hR powers hpowers
    pure hpure hbudget hfinite

end PiExponent.CurveNormalizedDegreeTransfer

end

end OAI
end


