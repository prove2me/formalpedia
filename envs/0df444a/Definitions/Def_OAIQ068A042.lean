-- Prove2me | Definitions.Def_OAIQ068A042
-- name    : OAIQ068A042
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:25:43.615996+00:00
-- url     : https://prove2.me/theorems/e2f4820b-339d-418f-a056-c2740bcb38f7
-- title:
--   Definitions bundle OAIQ068A042 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 34 declarations of OpenAI's Lean: 22 definitions, 1 instance and 11 theorems. The definitions and types are `OAI.PiExponent.CurveCycle.componentZeroPointEquiv`, `OAI.PiExponent.CurveCycle.componentZeroToGlobal`, `OAI.PiExponent.CurveCycle.sectionZeroIncidenceEquiv`, `OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainTwo`, `OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison.cochainZero`, `OAI.PiExponent.GeometrySupport.CechZeroAdditive.augmentationHom`, `OAI.PiExponent.GeometrySupport.CechZeroAdditive.sectionsEquiv`, `OAI.PiExponent.NumericalAmpleness.LineIsoInvariant`, `OAI.PiExponent.NumericalAmpleness.MixedDegreeLE`, `OAI.PiExponent.NumericalAmpleness.mixedDifference`, `OAI.PiExponent.NumericalAmpleness.mixedTop`, `OAI.PiExponent.NumericalAmpleness.pullbackCartierMiddleIso`, `OAI.PiExponent.NumericalAmpleness.pullbackMixedPowerIso`, `OAI.PiExponent.NumericalAmpleness.structureLineBundle`, `OAI.PiExponent.NumericalAmpleness.tensorDifference`, `OAI.PiExponent.NumericalAmpleness.tensorSectionComplex`, `OAI.PiExponent.NumericalAmpleness.tensorTwistSwapIso`, `OAI.PiExponent.ProjectiveGlobalPolynomials.globalCochain`, `OAI.PiExponent.ProjectiveGlobalPolynomials.globalLaurent`, `OAI.PiExponent.ReesSheafCechRecovery.schemeFreeOpen`, `OAI.PiExponentSeshadri.ComponentAmpleDescent.pullbackTwistIso`, `OAI.PiExponentSeshadri.Geometry.closedLineQuotientIso`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ComponentAmpleDescentCover`, `PiExponent_Approximation_ClosedUnitKernel`, `PiExponent_Approximation_SectionZeroSupport`, `PiExponent_Cohomology_CartierEulerPair`, `PiExponent_Cohomology_CechH1Transfer`, `PiExponent_Cohomology_CechZeroAdditive`, `PiExponent_Cohomology_EulerSupportDimension`, `PiExponent_Cohomology_EulerTwistTransport`, `PiExponent_Cohomology_MixedEulerAlgebra`, `PiExponent_Cohomology_MixedEulerPolarization`, `PiExponent_Cohomology_ReesSheafCechRecovery`, `PiExponent_Geometry_CurveComponentIncidence`, `PiExponent_Geometry_CurveComponentZeroPoints`, `PiExponent_Geometry_GeneralCartierDegreeLength`, `PiExponent_Geometry_ProjectiveGlobalPolynomials`.
--
--   **Imports.** It imports the bundles `OAIQ068A036`, `OAIQ068A037`, `OAIQ068A038` and `OAIQ068A039` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A043` and `OAIQ068A045`; the statements `OAI_PiExponent_CurveCycle_zero_lengthNat_eq_component_sum` and `OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68`; the proofs of `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_section_comparison`, `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_section_comparison_q68`, `OAI_PiExponent_CurveCycle_tensor_euler_margin`, `OAI.PiExponent.CurveCycle.tensor_euler_margin_q68`, `OAI_PiExponent_CurveCycle_zero_lengthNat_eq_component_sum`, `OAI.PiExponent.CurveCycle.zero_lengthNat_eq_component_sum_q68`, `OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample`, `OAI.PiExponent.NumericalAmpleness.curveDegree_pos_of_ample_q68`, `OAI_PiExponent_NumericalAmpleness_lineBundle_cohomology_zero_of_dimension_le`, `OAI.PiExponent.NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le_q68`, `OAI_PiExponent_NumericalAmpleness_regular_ample_sectionZero_dimension` and `OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A036
import Definitions.Def_OAIQ068A037
import Definitions.Def_OAIQ068A038
import Definitions.Def_OAIQ068A039

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ComponentAmpleDescentCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ComponentAmpleDescent
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open _root_.OAI.PiExponentSeshadri.Geometry
variable {X Y Z : Scheme.{0}}

def pullbackTwistIso (f : Y ⟶ X) (K L : LineBundle X) (n : ℕ) :
    ((K.tensor (L.pow n)).pullback f).sheaf ≅
      (moduleTwistFunctor (L.pullback f) n).obj (K.pullback f).sheaf :=
  PullbackTensor.iso f K (L.pow n) ≪≫
    moduleTensorIso (Iso.refl _) (PullbackTensor.powIso f L n) ≪≫
    (moduleTwistPowerIso (L.pullback f) (K.pullback f).sheaf n).symm

end
end PiExponentSeshadri.ComponentAmpleDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedUnitKernel
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open PiExponentSeshadri.TensorPure


variable {X Y : Scheme.{0}}

def closedLineQuotientIso (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensor X ((Scheme.Modules.pushforward f).obj (structureSheaf Y)) M.sheaf ≅
      (Scheme.Modules.pushforward f).obj (M.pullback f).sheaf :=
  PiExponent.ProjectionFormula.iso f (structureSheaf Y) M ≪≫
    (Scheme.Modules.pushforward f).mapIso (moduleTensorUnit (M.pullback f).sheaf)

theorem closedLineQuotientIso_map (f : Y ⟶ X) (M : LineBundle X) :
    moduleTensorMap (PiExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) ≫
      (closedLineQuotientIso f M).hom =
    (moduleTensorUnit M.sheaf).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf := by
  apply PiExponentSeshadri.TensorPure.hom_ext
  intro U a m
  let η := ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf).val.app (op U)
  have ht := map_pure (PiExponentSeshadri.IdealModule.structureMap f) (𝟙 M.sheaf) U a m
  have hp := PiExponent.ProjectionFormula.hom_pure f (structureSheaf Y) M.sheaf U
    ((PiExponentSeshadri.IdealModule.structureMap f).app U a) m
  have hu := unit_pure (M.pullback f).sheaf (f ⁻¹ᵁ U)
    ((PiExponentSeshadri.IdealModule.structureMap f).app U a) (η m)
  have hv := unit_pure M.sheaf U a m
  have hs := η.hom.map_smul a m
  exact (congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U)
      ((PiExponent.ProjectionFormula.hom f (structureSheaf Y) M.sheaf).app U z)) ht).trans
    ((congrArg (fun z => (moduleTensorUnit (M.pullback f).sheaf).hom.app (f ⁻¹ᵁ U) z) hp).trans
      (hu.trans (hs.symm.trans (congrArg (fun z => η z) hv).symm)))

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionZeroSupport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SectionZeroIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.InverseFrames PiExponent.SectionImageSupport
variable {X : Scheme.{0}}

theorem dualSection_isoOpen (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) = sectionOpen X s := by
  ext x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  change (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen (L.dualSection s) ↔
    (⟨x,hx⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ PiExponentSeshadri.SectionOpens.isoOpen s
  erw [isoOpen_preimage_on_frame (L.dualSection s) U
    (inverseOpenFrame (lineTensorInverseIso L) U e), dualSection_restrict_coefficient,
    preimage_isoOpen s U.ι e]

theorem zeroIdeal_support (L : LineBundle X) (s : GlobalSections X L.sheaf) :
    ((zeroIdeal L s).support : Set X) = (sectionOpen X s : Set X)ᶜ := by
  let := PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L.inverse
  let : SheafOfModules.IsQuasicoherent L.inverse.sheaf :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData L.inverse.sheaf).choose.isQuasicoherent
  change ((PiExponent.SectionImageIdeal.imageIdealSheaf (L.dualSection s)).support : Set X) = _
  rw [imageIdealSheaf_support, dualSection_isoOpen]

end
end PiExponent.SectionZeroIdeal

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CartierEulerPair
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem regular_tensorSection_restriction_shortExact
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] :
    ∃ hz : sectionMultiplyLeft A.sheaf F.sheaf s ≫
        PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F) = 0,
      (ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
        (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F)) hz).ShortExact := by
  let : Mono (moduleTensorMap s (𝟙 F.sheaf)) := moduleTensorMap_mono s F
  have hm : Mono (sectionMultiplyLeft A.sheaf F.sheaf s) := mono_comp _ _
  refine @PiExponentSeshadri.CartierSequence.exact X p F (A.tensor F)
    (sectionMultiplyLeft A.sheaf F.sheaf s) hm (zeroIdeal A s) ?_
  intro x
  obtain ⟨U, hx, ⟨a⟩, ⟨f⟩⟩ := common_affine_frames A F x
  refine ⟨U, hx, f, _root_.OAI.PiExponent.CartierPowerFrames.tensorFrame A.sheaf F.sheaf U.1 a f, ?_⟩
  exact (zeroIdeal_on_frame A s U a).trans
    (tensor_multiply_ideal A.sheaf F.sheaf s U a f).symm

def tensorSectionComplex (p : X ⟶ Spec (CommRingCat.of ℂ)) (A F : LineBundle X)
    (s : GlobalSections X A.sheaf) [Mono s] : ShortComplex X.Modules :=
  ShortComplex.mk (sectionMultiplyLeft A.sheaf F.sheaf s)
    (PiExponentSeshadri.LineClosedUnit.map (zeroIdeal A s).subschemeι (A.tensor F))
    (regular_tensorSection_restriction_shortExact p A F s).choose

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechH1Transfer
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X Y : Scheme.{u}} {J : Type u}

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup
  PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

namespace SectionComparison
variable {U : J → X.Opens} {V : J → Y.Opens} {M : X.Modules} {N : Y.Modules}
    (P : SectionComparison U V M N)

def cochainZero : CechHigher.Cochain X.ringCatSheaf U M 0 ≃+
    CechHigher.Cochain Y.ringCatSheaf V N 0 where
  toFun b t := P.vertex t (b t)
  invFun b t := (P.vertex t).symm (b t)
  left_inv b := by funext t; exact (P.vertex t).symm_apply_apply _
  right_inv b := by funext t; exact (P.vertex t).apply_symm_apply _
  map_add' b c := by funext t; exact map_add (P.vertex t) _ _

def cochainTwo : CechHigher.Cochain X.ringCatSheaf U M 2 →+
    CechHigher.Cochain Y.ringCatSheaf V N 2 where
  toFun b t := P.triple t (b t)
  map_zero' := by funext t; exact map_zero (P.triple t)
  map_add' b c := by funext t; exact map_add (P.triple t) _ _

end SectionComparison
end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechZeroAdditive
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechZeroAdditive
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def augmentationHom (V : Opens X) (hUV : ∀ i, U i ≤ V) :
    (freeOpen R V ⟶ M) →+ cycles R U M 0 where
  toFun f := ⟨augmentation R U M V hUV f, augmentation_closed R U M V hUV f⟩
  map_zero' := by
    apply Subtype.ext
    funext t
    exact comp_zero
  map_add' f g := by
    apply Subtype.ext
    funext t
    exact restrictHom_add R _ f g

def sectionsEquiv (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    (freeOpen R V ⟶ M) ≃+ cycles R U M 0 :=
  AddEquiv.ofBijective (augmentationHom R U M V hUV) ⟨by
    intro f g hfg
    exact CechZero.augmentation_injective R U M V hUV hcover (congrArg Subtype.val hfg), by
    intro c
    obtain ⟨f, hf⟩ := CechZero.augmentation_exists R U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem sectionsEquiv_val (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : freeOpen R V ⟶ M) :
    (sectionsEquiv R U M V hUV hcover f).val = augmentation R U M V hUV f := rfl

end
end PiExponent.GeometrySupport.CechZeroAdditive

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerSupportDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.unit_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal
open scoped nonZeroDivisors

variable {X : Scheme.{0}}

theorem regular_sectionZero_dimension_le (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d + 1) :
    topologicalKrullDim (zeroIdeal L s).subscheme ≤ d := by
  let I := zeroIdeal L s
  apply dimension_le_of_local_bound d
  intro y
  obtain ⟨V, hxV, ⟨eV⟩⟩ := L.locallyRankOne (I.subschemeι y)
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hxV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
  let f := I.subschemeCover.f U
  refine ⟨f.opensRange, ?_, ?_⟩
  · change y ∈ (I.subschemeCover.f U).opensRange
    rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
    exact hxW
  · have hr := section_affine_coefficient_nonZeroDivisor L s U e
    have hdrop := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
    rw [← zeroIdeal_on_frame L s U e] at hdrop
    have hring : ringKrullDim Γ(X,U) ≤ d + 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
      change topologicalKrullDim (Spec Γ(X,U)) ≤ d+1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ U.2.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hdim
    have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤ d := by
      have hbound := hdrop.trans hring
      exact ENat.WithBot.add_le_add_one_right_iff.mp hbound
    have hsource : topologicalKrullDim (Spec (I.subschemeCover.X U)) ≤ d := by
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).le.trans hquot
    change topologicalKrullDim f.opensRange.toScheme ≤ d
    exact (IsHomeomorph.topologicalKrullDim_eq _
      f.isoOpensRange.hom.homeomorph.isHomeomorph).symm.le.trans hsource

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_EulerTwistTransport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def pullbackMixedPowerIso (f : Y ⟶ X) (L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj ((L.pow n).tensor M).sheaf ≅
      (((L.pullback f).pow n).tensor (M.pullback f)).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f (L.pow n) M ≪≫
    moduleTensorIso (PiExponentSeshadri.PullbackTensor.powIso f L n) (Iso.refl _)

def pullbackCartierMiddleIso (f : Y ⟶ X) (A L M : LineBundle X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (A.tensor ((L.pow n).tensor M)).sheaf ≅
      (((L.pullback f).pow n).tensor ((A.pullback f).tensor (M.pullback f))).sheaf :=
  PiExponentSeshadri.PullbackTensor.iso f A ((L.pow n).tensor M) ≪≫
    moduleTensorIso (Iso.refl _) (pullbackMixedPowerIso f L M n) ≪≫
      cartierMiddlePowerIso (A.pullback f) (L.pullback f) (M.pullback f) n

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerAlgebra
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def LineIsoInvariant (f : LineBundle X → ℤ) : Prop :=
  ∀ L M, (L.sheaf ≅ M.sheaf) → f L = f M

def tensorDifference (L : LineBundle X) (f : LineBundle X → ℤ) : LineBundle X → ℤ :=
  fun M => f (L.tensor M) - f M

def mixedDifference : List (LineBundle X) → (LineBundle X → ℤ) → (LineBundle X → ℤ)
  | [], f => f
  | L :: ls, f => tensorDifference L (mixedDifference ls f)

@[simp] theorem mixedDifference_nil (f : LineBundle X → ℤ) : mixedDifference [] f = f := rfl
@[simp] theorem mixedDifference_cons (L : LineBundle X) (ls : List (LineBundle X))
    (f : LineBundle X → ℤ) :
    mixedDifference (L :: ls) f = tensorDifference L (mixedDifference ls f) := rfl

def tensorTwistSwapIso (L B M : LineBundle X) :
    (L.tensor (B.tensor M)).sheaf ≅ (B.tensor (L.tensor M)).sheaf :=
  (lineTensorAssoc L B M).symm ≪≫
    moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M

@[simp] theorem mixedDifference_zero (ls : List (LineBundle X)) :
    mixedDifference ls (0 : LineBundle X → ℤ) = 0 := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
      rw [mixedDifference_cons, ih]
      funext M
      exact sub_self _

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_MixedEulerPolarization
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def structureLineBundle (X : Scheme.{0}) : LineBundle X where
  sheaf := structureSheaf X
  locallyRankOne _x :=
    ⟨⊤, trivial, ⟨Scheme.Modules.restrictUnitIso (⊤ : X.Opens).ι⟩⟩

def MixedDegreeLE (d : ℕ) (f : LineBundle X → ℤ) : Prop :=
  ∀ ls : List (LineBundle X), ls.length = d+1 → mixedDifference ls f = 0

def mixedTop (f : LineBundle X → ℤ) (ls : List (LineBundle X)) : ℤ :=
  mixedDifference ls f (structureLineBundle X)

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechRecovery
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

end
end PiExponent.ReesSheafCechRecovery

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentZeroPoints
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

def componentZeroToGlobal {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subscheme := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  refine ⟨i (J.subschemeι z), ?_⟩
  have hz := z.property
  change J.subschemeι z ∈ (J.support : Set (reducedComponent X C)) at hz
  change i (J.subschemeι z) ∈ ((zeroIdeal L s).support : Set X)
  erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)] at hz
  erw [zeroIdeal_support L s]
  change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
  rw [pullback_isoOpen_eq L s i] at hz
  exact hz

theorem componentZeroToGlobal_mem {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ C.val :=
  reducedComponentι_mem X C _

def componentZeroPointEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X) :
    (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme ≃
    {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val} := by
  let i := reducedComponentι X C
  let I := zeroIdeal L s
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let g : J.subscheme → {y : I.subscheme // I.subschemeι y ∈ C.val} :=
    fun z => ⟨componentZeroToGlobal L s C z,componentZeroToGlobal_mem L s C z⟩
  apply Equiv.ofBijective g
  constructor
  · intro z w h
    apply J.subschemeι.isEmbedding.injective
    apply i.isEmbedding.injective
    exact congrArg (fun q => I.subschemeι q.val) h
  · intro y
    have hymem : I.subschemeι y.val ∈ Set.range i := by
      rw [reducedComponentι_range]
      exact y.property
    obtain ⟨z,hz⟩ := hymem
    have hzJ : z ∈ (J.support : Set (reducedComponent X C)) := by
      erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)]
      change z ∉ isoOpen (pullbackSection i s)
      rw [pullback_isoOpen_eq L s i]
      change i z ∉ isoOpen s
      rw [hz]
      have hy := y.val.property
      change I.subschemeι y.val ∈ (I.support : Set X) at hy
      erw [zeroIdeal_support L s] at hy
      exact hy
    refine ⟨⟨z,hzJ⟩, ?_⟩
    apply Subtype.ext
    apply I.subschemeι.isEmbedding.injective
    exact hz

instance finite_componentZero {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    [Finite (zeroIdeal L s).subscheme] :
    Finite (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
  Finite.of_equiv _ (componentZeroPointEquiv L s C).symm

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveComponentIncidence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

def sectionZeroIncidenceEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) :
    (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) ≃
    (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) where
  toFun p := ⟨p.2.val, (componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩⟩
  invFun q := ⟨(componentZeroPointEquiv L s q.1 q.2).val,
    ⟨q.1,(componentZeroPointEquiv L s q.1 q.2).property⟩⟩
  left_inv p := by
    rcases p with ⟨y,C,hC⟩
    dsimp only
    have h := (componentZeroPointEquiv L s C).apply_symm_apply ⟨y,hC⟩
    exact congrArg (fun t : {y : (zeroIdeal L s).subscheme //
      (zeroIdeal L s).subschemeι y ∈ C.val} =>
      (⟨t.val,⟨C,t.property⟩⟩ : Σ y : (zeroIdeal L s).subscheme,
        {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val})) h
  right_inv q := by
    rcases q with ⟨C,z⟩
    dsimp only
    exact congrArg (Sigma.mk C) ((componentZeroPointEquiv L s C).symm_apply_apply z)

end
end PiExponent.CurveCycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_GeneralCartierDegreeLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.GeneralCartierDegreeLength


theorem finite_zeroIdeal_of_mono {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    Finite (PiExponent.SectionZeroIdeal.zeroIdeal L s).subscheme := by
  let I := PiExponent.SectionZeroIdeal.zeroIdeal L s
  let q := I.subschemeι ≫ p
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace q
  let : IsNoetherian I.subscheme := {}
  exact PiExponent.NumericalAmpleness.finite_of_dim_le_zero
    (PiExponent.NumericalAmpleness.regular_sectionZero_dimension_le L s 0 (by simpa using hd))

end PiExponent.GeneralCartierDegreeLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomials
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveTwistCech ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

def globalCochain (U : σ → X.Opens) (M : X.Modules)
    (b : structureSheaf X ⟶ M) : CechHigher.Cochain X.ringCatSheaf U M 0 :=
  CechHigher.augmentation X.ringCatSheaf U M ⊤ (fun _ => le_top)
    ((PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b)

def globalLaurent (P : LaurentCechPresentation (K := R) U M (n : ℤ))
    (b : structureSheaf X ⟶ M) :
    ProjectiveMonomialCechHigher.Cochain σ (Laurent σ R (n : ℤ)) 0 :=
  P.toLaurent (globalCochain U M b)

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveCoordinateAcyclicity GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra


end
end PiExponent.ProjectiveGlobalPolynomials

end OAI
end


