-- Prove2me | Definitions.Def_OAIQ068A040
-- name    : OAIQ068A040
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:19:29.139798+00:00
-- url     : https://prove2.me/theorems/1213697e-d006-416c-9fc7-e2e52bb9fc83
-- title:
--   Definitions bundle OAIQ068A040 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 79 declarations of OpenAI's Lean: 24 definitions, 2 inductive types or structures, 4 instances and 49 theorems. The definitions and types are `OAI.PiExponent.AdmissibleBlowupGeometry.H`, `OAI.PiExponent.AdmissibleBlowupGeometry.ampleExponent`, `OAI.PiExponent.AdmissibleBlowupGeometry.interpolationBundle`, `OAI.PiExponent.AdmissibleBlowupGeometry.uniformMargin`, `OAI.PiExponent.AdmissibleBlowupMargin.AffineCurveDegreeData`, `OAI.PiExponent.AdmissibleCurveCoordinates.chart`, `OAI.PiExponent.AdmissibleCurveCoordinates.chartPresentation`, `OAI.PiExponent.AdmissibleCurveCoordinates.coordinates`, `OAI.PiExponent.AdmissibleCurveCoordinates.fieldEquiv`, `OAI.PiExponent.AdmissibleCurveCoordinates.imageAlgebra`, `OAI.PiExponent.AdmissibleCurveCoordinates.imageCoordinates`, `OAI.PiExponent.AdmissibleCurveCoordinates.imageCurve`, `OAI.PiExponent.AdmissibleCurveCoordinates.imageStructure`, `OAI.PiExponent.AdmissibleCurveImage.functionFieldIso`, `OAI.PiExponent.AdmissibleCurveImage.imageCurve`, `OAI.PiExponent.AdmissibleCurveModel.ModelData`, `OAI.PiExponent.BlowupCurveMargin.contactSum`, `OAI.PiExponent.CurveModelPlaces.chartCenter`, `OAI.PiExponent.CurveModelPlaces.laurentCenter`, `OAI.PiExponent.CurveModelPlaces.laurentValuationHom`, `OAI.PiExponent.CurveModelPlaces.placePoint`, `OAI.PiExponent.CurveModelPlaces.placesEquivNongenericPoints`, `OAI.PiExponent.CurvePlaceSectionDivisor.divisor`, `OAI.PiExponent.ExceptionalCurveDegree.inverseSection`, `OAI.PiExponentSeshadri.Projective.coordinateFramedLaurentPresentation`, `OAI.PiExponentSeshadri.Projective.negativeCoordinateLaurentPresentation`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_AdmissibleBlowupMargin`, `PiExponent_Ampleness_AdmissibleBlowupPolarization`, `PiExponent_Ampleness_BlowupAmpleTwist`, `PiExponent_Ampleness_BlowupCurveMargin`, `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_InverseFrameRestriction`, `PiExponent_Approximation_InverseFrames`, `PiExponent_Cohomology_CurveTwoAffineVanishing`, `PiExponent_Cohomology_ProjectiveFramedCech`, `PiExponent_Geometry_AdmissibleCurveCoordinates`, `PiExponent_Geometry_AdmissibleCurveImage`, `PiExponent_Geometry_AdmissibleCurveModel`, `PiExponent_Geometry_CoherentProjectiveFinite`, `PiExponent_Geometry_CurveModelPlaces`, `PiExponent_Geometry_CurvePlaceSectionDivisor`, `PiExponent_Geometry_PlaceLocalRing`, `PiExponent_Geometry_PlaceParameterModel`, `PiExponent_Geometry_ProjectiveCoordinateFinite`, `PiExponent_Geometry_ProjectiveFiniteCoordinates`, `PiExponent_Geometry_ProjectiveNegativeCoordinates`, `PiExponent_Geometry_ProjectiveNegativeFrames`, `PiExponent_Geometry_ProjectiveNegativeScalars`, `PiExponent_LocalAlgebra_CoherentExtFiniteness`, `PiExponent_LocalAlgebra_CoherentInverseFinite`.
--
--   **Imports.** It imports the bundles `OAIQ068A035`, `OAIQ068A036`, `OAIQ068A037` and `OAIQ068A038` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A043`, `OAIQ068A044` and `OAIQ068A045`; the statements `OAI_PiExponent_AdmissibleBlowupGeometry_uniform_curve_margin`, `OAI.PiExponent.AdmissibleBlowupGeometry.uniform_curve_margin_q68`, `OAI_PiExponent_CurveInequality_weighted_curve_inequality` and `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68`; the proofs of `OAI_PiExponentSeshadri_Geometry_isAffineOpen_of_fullSupport_preimage`, `OAI.PiExponentSeshadri.Geometry.isAffineOpen_of_fullSupport_preimage_q68`, `OAI_PiExponent_BlowupCurveMargin_margin_of_contracted`, `OAI.PiExponent.BlowupCurveMargin.margin_of_contracted_q68`, `OAI_PiExponent_BlowupCurveMargin_margin_of_image_outside_chart`, `OAI.PiExponent.BlowupCurveMargin.margin_of_image_outside_chart_q68`, `OAI_PiExponent_BlowupCurveMargin_margin_of_nonnegative_degree`, `OAI.PiExponent.BlowupCurveMargin.margin_of_nonnegative_degree_q68`, `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_section_comparison`, `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68`, `OAI_PiExponent_CurveCycle_tensor_euler_margin`, `OAI.PiExponent.CurveCycle.tensor_euler_margin_q68`, `OAI_PiExponent_CurveInequality_weighted_curve_inequality`, `OAI.PiExponent.CurveInequality.weighted_curve_inequality_q68`, `OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample`, `OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_isAmple_of_integral_closed_restrictions`, `OAI.PiExponent.NumericalAmpleness.isAmple_of_integral_closed_restrictions_q68`, `OAI_PiExponent_NumericalAmpleness_regular_ample_sectionZero_dimension` and `OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A035
import Definitions.Def_OAIQ068A036
import Definitions.Def_OAIQ068A037
import Definitions.Def_OAIQ068A038

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

theorem moduleTwistFunctor_shortExact (L : LineBundle X) (n : ℕ)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTwistFunctor L n)).ShortExact := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change ((S.map (moduleTwistFunctor L n)).map
      (moduleTensorRightFunctor L.sheaf)).ShortExact
    exact moduleTensorRightFunctor_shortExact L (S.map (moduleTwistFunctor L n)) ih

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceParameterModel
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.PlaceParameterModel
open CurveZeroPole CurveValuationCenter WeightedCurveDegree

theorem parameter_positive {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : 0 < p.valuation (parameter p) := by
  rw [parameter_value]
  norm_num

theorem parameter_transcendental
    {F E : Type*} [Field F] [IsAlgClosed F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : Transcendental F (parameter p) := by
  intro ha
  have hm : parameter p ∈ algebraicClosure F E := mem_algebraicClosure_iff.mpr ha
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure F E)] at hm
  obtain ⟨c, hc⟩ := hm
  change algebraMap F E c = parameter p at hc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact parameter_nonzero p hc.symm
  have hz := CurveProductFormula.valuation_constant_eq_zero p c hc0
  rw [hc, parameter_value] at hz
  exact one_ne_zero hz

end PiExponent.PlaceParameterModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceLocalRing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.infinityChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.infinityOverlap_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.parameterChartProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.zeroChartInclusion_isOpenImmersion _root_.OAI.PiExponent.CurveNormalizationModel.zeroOverlap_isOpenImmersion _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceLocalRing
open CurveZeroPole CurveValuationCenter PlaceParameterModel

theorem residue_integral
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)) := by
  let f := parameter p
  have hf : Transcendental ℂ f := parameter_transcendental p
  let := CurveParameterFinite.finiteDimensional_adjoin_singleton ℂ E htrdeg hf
  let := ParameterResidueField.parameterChartConstants f hf
  let q := parameterCenterPlace f hf p.valuation p.constants_nonneg (parameter_positive p)
  let := ParameterResidueField.parameter_residue_integral f hf q
  exact residue_integral_of_algEquiv (A := Localization.AtPrime q.1)
    (parameterCenterLocalAlgEquiv f hf p (parameter_positive p))

end PiExponent.PlaceLocalRing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

instance blowup_isIntegral : IsIntegral (blowup d) :=
  PiExponentSeshadri.BlowupGluing.scheme_isIntegral (centerIdeal d) (centerIdeal_support_ne_top d)
instance blowup_isLocallyNoetherian : IsLocallyNoetherian (blowup d) :=
  LocallyOfFiniteType.isLocallyNoetherian (structureMap d)
instance blowup_isNoetherian : IsNoetherian (blowup d) := {}

theorem isBlowup : IsBlowup (centerIdeal d) (projection d) :=
  PiExponentSeshadri.BlowupGluing.isBlowup (centerIdeal d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma pairingFrame_change_apply (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) (x : N.val.obj (op (⊤ : X.Opens))) :
    regularValue (pairingFrame E f).hom ⊤ x =
      (frameChange f e : Γ(X,⊤)) * regularValue (pairingFrame E e).hom ⊤ x := by
  dsimp only [regularValue]
  have hf := pairingFrame_apply E f ⊤ x
  have he := pairingFrame_apply E e ⊤ x
  have hg := congrArg (fun m => E.hom.app ⊤ (PiExponentSeshadri.TensorPure.pure M N ⊤ m x))
    (frame_generator_change e f)
  have hs := congrArg (fun z => E.hom.app ⊤ z)
    (pure_smul_left M N ⊤ (frameChange f e : Γ(X,⊤)) (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  have hm := E.hom.app_smul (r := (frameChange f e : Γ(X,⊤)))
    (x := PiExponentSeshadri.TensorPure.pure M N ⊤ (e.inv.app ⊤ (1 : Γ(X,⊤))) x)
  exact hf.trans (hg.trans (hs.trans (hm.trans
    (congrArg (fun a : Γ(X,⊤) => (frameChange f e : Γ(X,⊤)) * a) he.symm))))

lemma pairingFrame_frameChange (E : moduleTensor X M N ≅ O X)
    (e f : M ≅ O X) :
    frameChange (pairingFrame E e) (pairingFrame E f) = frameChange f e := by
  apply Units.ext
  change (pairingFrame E f).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  change regularValue (pairingFrame E f).hom ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = _
  erw [pairingFrame_change_apply]
  have h := congrArg (fun t => t.app ⊤ (1 : Γ(X,⊤))) (pairingFrame E e).inv_hom_id
  change (pairingFrame E e).hom.app ⊤ ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = (1 : Γ(X,⊤)) at h
  have hv : regularValue (pairingFrame E e).hom ⊤
      ((pairingFrame E e).inv.app ⊤ (1 : Γ(X,⊤))) = 1 := h
  rw [hv, mul_one]

lemma inverseOpenFrame_frameChange (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e f : M.restrict U.ι ≅ O U.toScheme) :
    frameChange (inverseOpenFrame E U e) (inverseOpenFrame E U f) = frameChange f e :=
  pairingFrame_frameChange (restrictPairing E U) e f

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveFramedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

attribute [local irreducible] coordinateFramedOverlap

def coordinateFramedLaurentPresentation
    (hres : ∀ i j (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
      (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
      (z : schemeFreeOpen_p0 (coordinateFiniteOpen M s i a) ⟶ N),
      coordinateFramedOverlap M s k hc f hf N e d j b
        (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      coordinateFramedOverlap M s k hc f hf N e d i a z) :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N d where
  coefficient := coordinateFramedTuple M s k hc f hf N e d
  injective := coordinateFramedTuple_injective M s k hc f hf N e d
  regular := coordinateFramedTuple_regular M s k hc f hf N e d
  surjective := coordinateFramedTuple_surjective M s k hc f hf N e d
  restriction q t j z := by
    change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
      (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)
        (freeOpenMap X.ringCatSheaf (homOfLE
          (PiExponent.GeometrySupport.CechHigher.faceLE (fun i => SectionOpens.isoOpen (s i)) t j)) ≫ z)) =
      coordinateFramedOverlap M s k hc f hf N e d ((t ∘ j.succAbove) 0)
        (tupleVariables (t ∘ j.succAbove) 0)
        (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s (t ∘ j.succAbove) 0) z)
    erw [freeOpenHomCongr_restrict]
    exact hres _ _ _ _ _ _

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_InverseFrameRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma inverseOpenFrame_pairing (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme)
    (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι,A)) (n : Γ(N.restrict U.ι,A)) :
    E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n) =
      regularValue e.hom A m * regularValue (inverseOpenFrame E U e).hom A n := by
  rw [← restrictPairing_pure]
  exact pairing_apply (restrictPairing E U) e A m n

lemma inverseOpenFrame_restrict_pairing (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (m : Γ(M.restrict V.ι,A)) (n : Γ(N.restrict V.ι,A)) :
    E.hom.app (V.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (V.ι ''ᵁ A) m n) =
      regularValue (restrictOpenFrame h e).hom A m *
        regularValue (restrictOpenFrame h (inverseOpenFrame E U e)).hom A n := by
  let B := X.homOfLE h ''ᵁ A
  have h₁ : V.ι ''ᵁ A ≤ U.ι ''ᵁ B := by simp [B, ← Scheme.Hom.comp_image]
  have h₂ : U.ι ''ᵁ B ≤ V.ι ''ᵁ A := by simp [B, ← Scheme.Hom.comp_image]
  let m' := M.presheaf.map (homOfLE h₂).op m
  let n' := N.presheaf.map (homOfLE h₂).op n
  have hp := inverseOpenFrame_pairing E U e B m' n'
  have hs := congrArg (fun x : Γ(U.toScheme,B) => X.presheaf.map (homOfLE h₁).op x) hp
  have hs := hs.trans ((X.presheaf.map (homOfLE h₁).op).hom.map_mul _ _)
  have hr := pairing_restrict E h₁ m' n'
  have hm : M.presheaf.map (homOfLE h₁).op m' = m := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) m = m
    exact CategoryTheory.congr_fun (restrictionMap_cycle M.presheaf h₂ h₁) m
  have hn : N.presheaf.map (homOfLE h₁).op n' = n := by
    change (N.presheaf.map _ ≫ N.presheaf.map _) n = n
    exact CategoryTheory.congr_fun (restrictionMap_cycle N.presheaf h₂ h₁) n
  rw [hm, hn] at hr
  dsimp only [regularValue]
  rw [restrictOpenFrame_app, restrictOpenFrame_app]
  exact hr.symm.trans hs

lemma inverseOpenFrame_restrict (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (inverseOpenFrame E U e) =
      inverseOpenFrame E V (restrictOpenFrame h e) := by
  apply Iso.ext
  ext A n
  let eV := restrictOpenFrame h e
  have h1 := inverseOpenFrame_restrict_pairing E h e A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have h2 := inverseOpenFrame_pairing E V eV A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have he : regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) = (1 : Γ(V.toScheme,A)) :=
    congrArg (fun g => g.app A (1 : Γ(V.toScheme,A))) eV.inv_hom_id
  change _ = regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) * _ at h1
  rw [he, one_mul] at h1 h2
  exact h1.symm.trans h2

end
end PiExponent.InverseFrames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.InverseFrames
variable {X : Scheme} {M N : X.Modules}

lemma negativeCoordinateFrame_frameChange (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    W.topIso.hom
      (frameChange (restrictOpenFrame hi (negativeCoordinateFrame n E si))
        (restrictOpenFrame hj (negativeCoordinateFrame n E sj)) : Γ(W.toScheme,⊤)) =
      coordinateRatioOn si sj hi ^ n := by
  have h := (congrArg₂
    (fun e f : N.restrict W.ι ≅ O W.toScheme => frameChange e f)
    (inverseOpenFrame_restrict E hi (coordinatePowerFrame si n))
    (inverseOpenFrame_restrict E hj (coordinatePowerFrame sj n))).trans
      (inverseOpenFrame_frameChange E W _ _)
  have hv := congrArg
    (fun z : Γ(W.toScheme,⊤)ˣ => W.topIso.hom (z : Γ(W.toScheme,⊤))) h
  refine hv.trans ?_
  erw [coordinatePowerFrame_frameChange, map_pow, topIso_hom_restrict]
  rfl

lemma negativeCoordinateFrame_hom_change_restrict (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {U W : X.Opens} (hi : U ≤ SectionOpens.isoOpen si)
    (hj : W ≤ SectionOpens.isoOpen sj) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ N) :
    framedHomCoefficientsEquiv W N (restrictOpenFrame hj (negativeCoordinateFrame n E sj))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      coordinateRatioOn si sj (h.trans hi) ^ n * X.presheaf.map (homOfLE h).op
        (framedHomCoefficientsEquiv U N (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b) := by
  erw [framedHomCoefficientsEquiv_change W N
    (restrictOpenFrame (h.trans hi) (negativeCoordinateFrame n E si)),
    negativeCoordinateFrame_frameChange]
  congr 1
  have hr := framedHomCoefficientsEquiv_restrict N h
    (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b
  rw [restrictOpenFrame_trans] at hr
  exact hr

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeCoordinates
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)

lemma negativeCoordinateOverlap_restrict (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : freeOpen X.ringCatSheaf (coordinateFiniteOpen M s i a) ⟶ N) :
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) j b (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) i a z := by
  let ci := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) N
    (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s i))) z
  let ri := coordinateFiniteRingEquiv M s k hc f hf i a
  let rj := coordinateFiniteRingEquiv M s k hc f hf j b
  let u := coordinateRatioOn (s i) (s j) (h.trans inf_le_left)
  have ht : coordinateFiniteTransition M s k hc f hf i j a b h (ri ci) =
      rj (X.presheaf.map (homOfLE h).op ci) := by
    simp only [coordinateFiniteTransition, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ri, RingEquiv.symm_apply_apply, rj]
  dsimp only [coordinateFramedOverlap, framedLaurentOverlap, framedHomRingEquiv]
  dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.trans_apply, RingEquiv.coe_toAddEquiv]
  change overlapLaurent j (-(n : ℤ)) b
    (rj (framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z))) =
    overlapLaurent i (-(n : ℤ)) a (ri ci)
  have hcoef : framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      u ^ n * X.presheaf.map (homOfLE h).op ci :=
    negativeCoordinateFrame_hom_change_restrict n E (s i) (s j)
      (U := coordinateFiniteOpen M s i a) (W := coordinateFiniteOpen M s j b)
      inf_le_left inf_le_left h z
  rw [hcoef, map_mul, map_pow]
  change overlapLaurent j (-(n : ℤ)) b
    ((rj u) ^ n * rj (X.presheaf.map (homOfLE h).op ci)) = _
  rw [← ht]
  exact coordinateNegativeLaurent_change M s k hc f hf n i j a b h (ri ci)

def negativeCoordinateLaurentPresentation :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N (-(n : ℤ)) :=
  coordinateFramedLaurentPresentation M s k hc f hf N
    (fun i => negativeCoordinateFrame n E (s i)) (-(n : ℤ))
    (negativeCoordinateOverlap_restrict M s k hc f hf n N E)

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveNegativeScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] coordinateFramedTuple negativeCoordinateFrame

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)

attribute [local instance] OAI.PiExponentSeshadri.Projective.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1
lemma negativeCoordinateLaurentPresentation_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : schemeFreeOpen_p3 X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t ((k c) • b) =
      c • (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t b :=
  coordinateFramedTuple_smul M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
    (-(n : ℤ)) q t c b

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentExtFiniteness
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

variable {X : Scheme.{0}}

theorem coherent_cohomology_finite_of_presentations
    [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (l : ℕ) (hl : 0 < l) (U : Fin l → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (presentation : ∀ (M : X.Modules) [M.IsFinitePresentation],
      Nonempty (CoherentFinitePresentation p M))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  let := sheafComplexLinear p
  let F : {N : X.Modules // N.IsFinitePresentation} → X.Modules := Subtype.val
  let P (i : {N : X.Modules // N.IsFinitePresentation}) :
      FiniteCohomologyPresentation (K := ℂ) (structureSheaf X) F i := by
    letI : i.val.IsFinitePresentation := i.property
    let S := Classical.choice (presentation i.val)
    exact
      { kernel := ⟨S.kernel, S.kernel_coherent⟩
        middle := S.middle
        left := S.left
        right := S.right
        comp_zero := S.comp_zero
        shortExact := S.shortExact
        finite := fun n => by
          change @Module.Finite ℂ (cohomology S.middle n) _ _ (complexExtModule p S.middle n)
          rw [complexExtModule_eq]
          exact S.middle_finite n }
  have hbound : ∀ i n, l ≤ n → ∀ x : Ext.{1} (structureSheaf X) (F i) n, x = 0 := by
    intro i n hn x
    let : i.val.IsFinitePresentation := i.property
    let : i.val.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData i.val).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover i.val n hn x
  have hf := ext_finite_of_presentations (K := ℂ) (structureSheaf X) F l hbound P
    ⟨M, inferInstance⟩ q
  change @Module.Finite ℂ (cohomology M q) _ _ (complexExtModule p M q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

end
end PiExponent.CoherentExtFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CoherentProjectiveFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  apply CoherentExtFiniteness.coherent_cohomology_finite_of_presentations p
    l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover _ M q
  intro A hA
  obtain ⟨n, hn⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A s hcover haffine
  obtain ⟨g, hg⟩ := hn n le_rfl
  let : g.IsFiniteType := hg
  exact ⟨NegativeTwistPresentations.coherentFinitePresentation L (N n) g (hpair n) p
    (hfinite n)⟩

end
end PiExponent.CoherentProjectiveFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentInverseFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q,
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) :=
  coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q

end
end PiExponent.CoherentProjectiveFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFinite
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] negativeCoordinateLaurentPresentation
  coordinateFramedTuple negativeCoordinateFrame LineBundle.inverse lineTensorInverseIso
variable {X Y : Scheme.{0}} {K σ : Type} [Field K] [Fintype σ]

theorem inversePower_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundle X) (s : σ → (structureSheaf X ⟶ L.sheaf)) (k : K →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
    (n q : ℕ) :
    letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) k
    Module.Finite K (cohomology (L.pow n).inverse.sheaf q) := by
  let := LineBundleCoherent.lineBundle_isFinitePresentation (L.pow n).inverse
  let : (L.pow n).inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (L.pow n).inverse.sheaf).choose.isQuasicoherent
  exact ActualLaurentExtFinite.cohomology_finite k
    (negativeCoordinateLaurentPresentation L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    (negativeCoordinateLaurentPresentation_smul L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    hc.ge
    (fun r t => IsAffineOpen.iInf
      (fun i => coordinateOpen_isAffine L.sheaf s k hc f hf (t i))) q

end
end PiExponent.GeometrySupport.ProjectiveCoordinateFinite

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFiniteCoordinates
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

namespace CohomologyFiniteness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {σ : Type} [Fintype σ] [Nonempty σ]

theorem finiteIndex_coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : σ → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ σ))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q := by
  let e := Fintype.equivFin σ
  let t : Fin (Fintype.card σ) → (structureSheaf X ⟶ L.sheaf) := fun i => s (e.symm i)
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (Equiv.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j)) e.symm).trans hc
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L (Fintype.card σ) Fintype.card_pos t ht
    (fun i => GeometrySupport.ProjectiveTupleCharts.coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf (e.symm i))
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end CohomologyFiniteness

namespace ProjectiveFiniteCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}} {σ : Type} [Finite σ] [Nonempty σ]

theorem projectiveSpace_cohomology_finite
    (M : (projectiveSpace ℂ σ).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ σ) M q := by
  let : Fintype σ := Fintype.ofFinite σ
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ σ) (K := ℂ) (σ := σ)
      (M := (lineBundle (R := ℂ) (σ := σ)).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ σ))
      (coordinateSection (R := ℂ) (σ := σ))
      (coordinateSection_cover (R := ℂ) (σ := σ)) =
      (Iso.refl (projectiveSpace ℂ σ)).hom :=
    coordinate_sectionsMorphism_identity (R := ℂ) (σ := σ)
  exact finiteIndex_coordinateBundle_finite (X := projectiveSpace ℂ σ)
    (polynomialProjectiveProjection ℂ σ)
    (lineBundle (R := ℂ) (σ := σ)) (coordinateSection (R := ℂ) (σ := σ))
    (coordinateSection_cover (R := ℂ) (σ := σ))
    (Iso.refl (projectiveSpace ℂ σ)) hid M q

theorem projectiveEmbedding_cohomology_finite
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ σ))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ σ) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ σ) M q
      (projectiveSpace_cohomology_finite ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ))
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ σ = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite i M q

end ProjectiveFiniteCoordinates

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupCurveMargin
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.blowup_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_compact _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isIntegral _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isLocallyNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_isNoetherian _root_.OAI.PiExponent.AdmissibleBlowupGeometry.compactification_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.index_nonempty _root_.OAI.PiExponent.AdmissibleBlowupGeometry.projection_proper _root_.OAI.PiExponent.AdmissibleBlowupGeometry.structureMap_proper _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.BlowupCurveMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open NumericalAmpleness
variable {B X : Scheme.{0}}

variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]

def contactSum (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ℝ :=
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  ∑ q ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
    (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights q : ℝ)


end PiExponent.BlowupCurveMargin

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveTwoAffineVanishing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveTwoAffineVanishing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem cohomology_subsingleton (U V : X.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology M n) := by
  let D : Fin 2 → X.Opens := ![U,V]
  have hD : ∀ i, IsAffineOpen (D i) := by
    intro i
    fin_cases i
    · exact hU
    · exact hV
  have hc : (⨆ i, D i) = ⊤ := by
    calc
      (⨆ i, D i) = U ⊔ V := le_antisymm
        (iSup_le (fun i => by
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right))
        (sup_le (le_iSup D 0) (le_iSup D 1))
      _ = ⊤ := hcover
  exact ⟨fun x y =>
    (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn x).trans
      (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn y).symm⟩

end PiExponent.CurveTwoAffineVanishing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelPlaces
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap_isProper _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.CurveModelPlaces
universe u
open CurveZeroPole CurveValuationCenter WeightedCurveDegree
open CurveNormalizationModel PlaceParameterModel
open AlgebraicGeometry CategoryTheory

theorem parameterValuationCenter_ne_bot
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    parameterValuationCenter f hf p.valuation p.constants_nonneg hp ≠ ⊥ := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective S (parameter p)
  have hbE : algebraMap S E b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective S E)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)
  have haE : algebraMap S E a ≠ 0 := by
    intro ha
    rw [ha, zero_div] at hab
    exact parameter_nonzero p hab.symm
  have hbval : 0 ≤ p.valuation (algebraMap S E b) :=
    parameterChart_mem_valuationSubring f hf p.valuation p.constants_nonneg hp b
  have hmul : parameter p * algebraMap S E b = algebraMap S E a :=
    (eq_div_iff hbE).mp hab.symm
  have hapos : 0 < p.valuation (algebraMap S E a) := by
    rw [← hmul, p.valuation.map_mul, parameter_value]
    exact lt_of_lt_of_le (by norm_num : (0 : WithTop ℤ) < 1)
      (le_add_of_nonneg_right hbval)
  have hamem : a ∈ parameterValuationCenter f hf p.valuation p.constants_nonneg hp :=
    (mem_parameterValuationCenter_iff f hf p.valuation p.constants_nonneg hp a).mpr hapos
  intro hzero
  rw [hzero, Ideal.mem_bot] at hamem
  exact haE (by rw [hamem, map_zero])

def chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) where
  asIdeal := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  isPrime := inferInstance
  ne_bot := parameterValuationCenter_ne_bot f hf p hp

theorem valuation_eq_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    p.valuation = chartValuation f hf (chartCenter f hf p hp) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S
    (parameterValuationCenter_ne_bot f hf p hp) A
  change p.valuation = CurveLocalOrder.fractionAddValuation A E
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · exact parameterCenterLocal_nonneg f hf p.valuation p.constants_nonneg hp
  · intro a ha _
    exact parameterCenterLocal_positive f hf p.valuation p.constants_nonneg hp a ha
  · exact p.normalized

@[simp] theorem chartPlace_chartCenter
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) :
    chartPlace f hf (chartCenter f hf p hp) = p :=
  NormalizedPlace.ext (valuation_eq_chartCenter f hf p hp).symm

@[simp] theorem chartCenter_chartPlace
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf)) :
    chartCenter f hf (chartPlace f hf q) (chartPlace_parameter_nonneg f hf q) = q := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  ext a
  exact (mem_parameterValuationCenter_iff f hf (chartPlace f hf q).valuation
    (chartPlace f hf q).constants_nonneg (chartPlace_parameter_nonneg f hf q) a).trans
      (chartValuation_positive_iff f hf q a)

theorem parameterLaurentMap_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : LaurentPolynomial F) :
    parameterLaurentMap f hf a ∈ p.valuation.toValuation.valuationSubring := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [map_add]
    exact p.valuation.toValuation.valuationSubring.toSubring.add_mem ha hb
  | C_mul_T n c =>
    by_cases hn : 0 ≤ n
    · lift n to ℕ using hn
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hp n)
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat (le_of_not_ge hn)
      rw [parameterLaurentMap, LaurentPolynomial.eval₂_C_mul_T_neg_n]
      exact p.valuation.toValuation.valuationSubring.toSubring.mul_mem
        (p.constants_nonneg c)
        (p.valuation.toValuation.valuationSubring.toSubring.pow_mem hpinv k)

theorem parameterLaurentChart_mem
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹)
    (a : parameterLaurentChart f hf) :
    (a : E) ∈ p.valuation.toValuation.valuationSubring := by
  let := parameterLaurentAlgebra f hf
  exact integral_mem_valuationSubring p.valuation.toValuation
    (parameterLaurentMap_mem f hf p hp hpinv) a.property

def laurentValuationHom
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    parameterLaurentChart f hf →+* p.valuation.toValuation.valuationSubring where
  toFun a := ⟨a, parameterLaurentChart_mem f hf p hp hpinv a⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

def laurentCenter
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    PrimeSpectrum (parameterLaurentChart f hf) :=
  ⟨(IsLocalRing.maximalIdeal p.valuation.toValuation.valuationSubring).comap
    (laurentValuationHom f hf p hp hpinv), inferInstance⟩

theorem laurentCenter_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem laurentCenter_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    infinityOverlap f hf (laurentCenter f hf p hp hpinv) =
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  apply PrimeSpectrum.ext
  ext a
  rfl

theorem center_images_eq
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) (hpinv : 0 ≤ p.valuation f⁻¹) :
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ =
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hpinv, inferInstance⟩ := by
  rw [← laurentCenter_zero f hf p hp hpinv, ← laurentCenter_infinity f hf p hp hpinv]
  exact congrArg (fun g => g (laurentCenter f hf p hp hpinv))
    (parameterCurve_overlap_compatibility f hf)

theorem regular_iff_inverse_not_positive
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0) :
    0 ≤ p.valuation f ↔ ¬ 0 < p.valuation f⁻¹ := by
  let z := Units.mk0 f hf
  change 0 ≤ p.valuation (z : E) ↔ ¬ 0 < p.valuation ((z : E)⁻¹)
  rw [← Units.val_inv_eq_inv_val, ← coe_integerOrder, ← coe_integerOrder, integerOrder_inv]
  change ((0 : ℤ) : WithTop ℤ) ≤ (integerOrder p.valuation z : WithTop ℤ) ↔
    ¬ ((0 : ℤ) : WithTop ℤ) < (-integerOrder p.valuation z : ℤ)
  rw [WithTop.coe_le_coe, WithTop.coe_lt_coe]
  omega

theorem inverse_positive_of_not_regular
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (f : E) (hf : f ≠ 0)
    (hp : ¬ 0 ≤ p.valuation f) : 0 < p.valuation f⁻¹ := by
  exact Classical.not_not.mp ((not_congr (regular_iff_inverse_not_positive p f hf)).mp hp)

def placePoint
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) : parameterCurve f hf :=
  if hp : 0 ≤ p.valuation f then
    zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩
  else
    infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg (inverse_positive_of_not_regular p f hf.ne_zero hp).le,
        inferInstance⟩

theorem placePoint_eq_zero
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f) :
    placePoint f hf p = zeroChartInclusion f hf
      ⟨parameterValuationCenter f hf p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  simp only [placePoint, dite_eq_left hp]

theorem placePoint_eq_infinity
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E)
    (hp : 0 ≤ p.valuation f⁻¹) :
    placePoint f hf p = infinityChartInclusion f hf
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hp, inferInstance⟩ := by
  by_cases h : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p h]
    exact center_images_eq f hf p h hp
  · simp only [placePoint, dite_eq_right h]

theorem placePoint_ne_genericPoint
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) : placePoint f hf p ≠ genericPoint (parameterCurve f hf) := by
  by_cases hp : 0 ≤ p.valuation f
  · rw [placePoint_eq_zero f hf p hp]
    intro h
    have hq := (zeroChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f hf p hp (congrArg PrimeSpectrum.asIdeal hq)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hi := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    rw [placePoint_eq_infinity f hf p hi]
    intro h
    have hq := (infinityChartInclusion f hf).injective
      (h.trans (genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)).symm)
    rw [genericPoint_eq_bot_of_affine] at hq
    exact parameterValuationCenter_ne_bot f⁻¹ (transcendental_inverse f hf) p hi
      (congrArg PrimeSpectrum.asIdeal hq)

theorem regular_center_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p q : NormalizedPlace F E) (hp : 0 ≤ p.valuation f) (hq : 0 ≤ q.valuation f)
    (h : parameterValuationCenter f hf p.valuation p.constants_nonneg hp =
      parameterValuationCenter f hf q.valuation q.constants_nonneg hq) : p = q := by
  have hc : chartCenter f hf p hp = chartCenter f hf q hq :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  calc
    p = chartPlace f hf (chartCenter f hf p hp) := (chartPlace_chartCenter f hf p hp).symm
    _ = chartPlace f hf (chartCenter f hf q hq) := congrArg (chartPlace f hf) hc
    _ = q := chartPlace_chartCenter f hf q hq

theorem placePoint_mem_zero_iff
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) (p : NormalizedPlace F E) :
    placePoint f hf p ∈ Set.range (zeroChartInclusion f hf) ↔ 0 ≤ p.valuation f := by
  constructor
  · intro h
    by_contra hp
    have hi := inverse_positive_of_not_regular p f hf.ne_zero hp
    let q : PrimeSpectrum (parameterChart f⁻¹ (transcendental_inverse f hf)) :=
      ⟨parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le, inferInstance⟩
    have he : placePoint f hf p = infinityChartInclusion f hf q :=
      placePoint_eq_infinity f hf p hi.le
    have hm : infinityChartInclusion f hf q ∈ Set.range (zeroChartInclusion f hf) := he ▸ h
    have ho := (infinityChart_mem_zero_iff f hf q).mp hm
    let := parameterPolynomialAlgebra f⁻¹ (transcendental_inverse f hf)
    have h := (congrArg (fun s => q ∈ s) (infinityOverlap_range f hf)).mp ho
    change algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf)) Polynomial.X ∉
      parameterValuationCenter f⁻¹ (transcendental_inverse f hf)
        p.valuation p.constants_nonneg hi.le at h
    apply h
    rw [mem_parameterValuationCenter_iff]
    have hmap : ((algebraMap F[X] (parameterChart f⁻¹ (transcendental_inverse f hf))
        Polynomial.X) : E) = f⁻¹ := by
      change algebraMap F[X] E Polynomial.X = f⁻¹
      rw [parameterPolynomialAlgebra_map, Polynomial.aeval_X]
    exact (congrArg (fun a : E => 0 < p.valuation a) hmap).mpr hi
  · intro hp
    rw [placePoint_eq_zero f hf p hp]
    exact ⟨_, rfl⟩

theorem placePoint_injective
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    Function.Injective (placePoint f hf) := by
  intro p q h
  have hreg : (0 ≤ p.valuation f) ↔ (0 ≤ q.valuation f) := by
    rw [← placePoint_mem_zero_iff f hf p, ← placePoint_mem_zero_iff f hf q, h]
  by_cases hp : 0 ≤ p.valuation f
  · have hq := hreg.mp hp
    rw [placePoint_eq_zero f hf p hp, placePoint_eq_zero f hf q hq] at h
    have hc := (zeroChartInclusion f hf).injective h
    exact regular_center_injective f hf p q hp hq (congrArg PrimeSpectrum.asIdeal hc)
  · have hq : ¬ 0 ≤ q.valuation f := fun hq => hp (hreg.mpr hq)
    have hip := (inverse_positive_of_not_regular p f hf.ne_zero hp).le
    have hiq := (inverse_positive_of_not_regular q f hf.ne_zero hq).le
    rw [placePoint_eq_infinity f hf p hip, placePoint_eq_infinity f hf q hiq] at h
    have hc := (infinityChartInclusion f hf).injective h
    let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    exact regular_center_injective f⁻¹ (transcendental_inverse f hf) p q hip hiq
      (congrArg PrimeSpectrum.asIdeal hc)

theorem exists_placePoint_eq
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (x : parameterCurve f hf) (hx : x ≠ genericPoint (parameterCurve f hf)) :
    ∃ p : NormalizedPlace F E, placePoint f hf p = x := by
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint (Spec (.of (parameterChart f hf))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (zeroChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum (parameterChart f hf) :=
      ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f hf Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_zero f hf p (chartPlace_parameter_nonneg f hf Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f hf Q)
  · let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    have hq : q.asIdeal ≠ ⊥ := by
      intro h
      have heq : q = genericPoint
          (Spec (.of (parameterChart f⁻¹ (transcendental_inverse f hf)))) := by
        rw [genericPoint_eq_bot_of_affine]
        exact PrimeSpectrum.ext h
      apply hx
      rw [heq]
      exact genericPoint_eq_of_isOpenImmersion (infinityChartInclusion f hf)
    let Q : IsDedekindDomain.HeightOneSpectrum
        (parameterChart f⁻¹ (transcendental_inverse f hf)) := ⟨q.asIdeal, q.isPrime, hq⟩
    let p := chartPlace f⁻¹ (transcendental_inverse f hf) Q
    refine ⟨p, ?_⟩
    rw [placePoint_eq_infinity f hf p
      (chartPlace_parameter_nonneg f⁻¹ (transcendental_inverse f hf) Q)]
    congr 1
    apply PrimeSpectrum.ext
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal
      (chartCenter_chartPlace f⁻¹ (transcendental_inverse f hf) Q)

def placesEquivNongenericPoints
    {F E : Type u} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    NormalizedPlace F E ≃ {x : parameterCurve f hf // x ≠ genericPoint (parameterCurve f hf)} :=
  Equiv.ofBijective (fun p => ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩) ⟨
    fun _ _ h => placePoint_injective f hf (congrArg Subtype.val h),
    fun x => by
      obtain ⟨p, hp⟩ := exists_placePoint_eq f hf x.1 x.2
      exact ⟨p, Subtype.ext hp⟩⟩

end PiExponent.CurveModelPlaces

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurvePlaceSectionDivisor
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

def divisor (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    NormalizedPlace ℂ E →₀ ℕ :=
  Finsupp.domCongr (placesEquivNongenericPoints f hf).symm
    (SectionOrderDivisor.divisor (parameterCurveStructureMap f hf)
      (parameterCurve_dimension_le_one f hf) (parameterCurve_stalkDVR f hf) L s hs)

@[simp] theorem divisor_apply (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E) :
    divisor f hf L s hs p =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  rfl

end PiExponent.CurvePlaceSectionDivisor

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupMargin
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupMargin
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open AdmissibleBlowupGeometry BlowupCurveMargin
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

structure AffineCurveDegreeData (C : IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  y : E
  x : Fin d.m → E
  coordinates_generate : IntermediateField.adjoin ℂ
    (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  hyperplane_degree : (curveDegree (structureMap d) (A d) C : ℝ) =
    ((scale d).radius : ℝ) * poleDegree d y x trdeg_one
  exceptional_degree : (curveDegree (structureMap d) (J d) C : ℝ) =
    -((scale d).radius : ℝ) * contactSum d y x coordinates_generate trdeg_one

end PiExponent.AdmissibleBlowupMargin

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupAmpleTwist
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]

theorem exists_ample_exceptional_power_gt_one (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) (L : LineBundle X) (hL : L.IsAmple) :
    ∃ a : ℕ, 1 < a ∧
      (((L.pullback (projection I)).pow a).tensor (exceptionalLineBundle I)).IsAmple := by
  let := scheme_isIntegral I hI
  let : CompactSpace (scheme I) := QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact (isBlowup I).exists_ample_exceptional_power_gt_one L hL
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupPolarization
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

theorem exists_ampleExponent : ∃ a : ℕ, 1 < a ∧ (((A d).pow a).tensor (J d)).IsAmple :=
  PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    (centerIdeal d) (centerIdeal_support_ne_top d) (hyperplane d) (hyperplane_ample d)

def ampleExponent : ℕ := (exists_ampleExponent d).choose

def H : LineBundle (blowup d) := ((A d).pow (ampleExponent d)).tensor (J d)

theorem H_ample : (H d).IsAmple := (exists_ampleExponent d).choose_spec.2

def interpolationBundle : LineBundle (blowup d) := (A d).tensor (J d)

def uniformMargin : ℝ := BlowupCurveMargin.marginCoefficient (ampleExponent d) d.sigma

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
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

def inverseSection (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) :
    GlobalSections Y J.inverse.sheaf :=
  (lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveImage
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.AdmissibleCurveImage
open AdmissibleBlowupGeometry CurveBlowupImage
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

instance projection_restrict_isIso :
    IsIso (projection d ∣_ (centerIdeal d).support.compl) :=
  blowup_restrict_isIso (isBlowup d)

abbrev imageCurve (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :=
  CurveBlowupImage.imageCurve (projection d) C hn

def functionFieldIso (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    (imageCurve d C hn).scheme.functionField ≅ C.scheme.functionField :=
  imageFunctionFieldIso (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem functionFieldIso_generic (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x}) :
    Spec.map (functionFieldIso d C hn).hom ≫
      (imageCurve d C hn).scheme.fromSpecStalk (genericPoint (imageCurve d C hn).scheme) ≫
      (imageCurve d C hn).embedding =
    C.scheme.fromSpecStalk (genericPoint C.scheme) ≫ C.embedding ≫ projection d :=
  imageFunctionFieldIso_generic (projection d) C hn (centerIdeal d).support.compl
    (meets_center_complement d C hn)

theorem image_meets_chart (C : NumericalAmpleness.IntegralCurve (blowup d))
    (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange) :
    ∃ c : (imageCurve d C hn).scheme,
      (imageCurve d C hn).embedding c ∈ (affineChart d).opensRange := by
  obtain ⟨c,hc⟩ := hm
  refine ⟨CurveBlowupImage.imageMap (projection d) C hn c, ?_⟩
  simpa only [← Scheme.Hom.comp_apply, CurveBlowupImage.imageMap_comp] using hc

end PiExponent.AdmissibleCurveImage

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveCoordinates
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry
open CurveImageAffineCoordinates
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
variable (C : NumericalAmpleness.IntegralCurve (blowup d))
variable (hn : ¬ ∃ x : compactification d, Set.range (C.embedding ≫ projection d) ⊆ {x})

abbrev imageCurve := AdmissibleCurveImage.imageCurve d C hn
abbrev imageStructure := (imageCurve d C hn).embedding ≫ compactificationStructureMap d
@[instance_reducible] def imageAlgebra :
    Algebra ℂ (imageCurve d C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure d C hn)

def fieldEquiv :
    letI := imageAlgebra d C hn
    letI := sourceAlgebra d C
    (imageCurve d C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure d C hn) (sourceStructure d C)
    (AdmissibleCurveImage.functionFieldIso d C hn) (by
      simpa only [imageStructure, sourceStructure, structureMap, Category.assoc] using
        congrArg (fun f => f ≫ compactificationStructureMap d)
          (AdmissibleCurveImage.functionFieldIso_generic d C hn))

abbrev chart := affinePart (imageCurve d C hn).embedding (affineChart d)
abbrev chartPresentation := affinePresentation (imageCurve d C hn).embedding (affineChart d)

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection d) c ∈ (affineChart d).opensRange)

include hm in
theorem chart_nonempty : Nonempty (chart d C hn).1 :=
  affinePart_nonempty _ _ (AdmissibleCurveImage.image_meets_chart d C hn hm)

def imageCoordinates : Fin (d.m+1) → (imageCurve d C hn).scheme.functionField :=
  letI := chart_nonempty d C hn hm
  CurveImageAffineCoordinates.coordinates (chart d C hn) (chartPresentation d C hn)

def coordinates : Fin (d.m+1) → C.scheme.functionField :=
  letI := imageAlgebra d C hn
  letI := sourceAlgebra d C
  fieldEquiv d C hn ∘ imageCoordinates d C hn hm

end PiExponent.AdmissibleCurveCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveModel
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleCurveModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AdmissibleBlowupGeometry CurveNormalizationModel
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

structure ModelData (C : NumericalAmpleness.IntegralCurve (blowup d)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (d.m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ structureMap d =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ projection d) =
    CurveMonomialMap.genericMonomialMap (exponents d) (constantIndex d)
      ((scale d).exponents_constant d.curveDegreeWeights_pos) (coordinateIndex d)
      ((scale d).exponents_coordinate d.curveDegreeWeights_pos) coordinates

end PiExponent.AdmissibleCurveModel

end

end OAI
end


