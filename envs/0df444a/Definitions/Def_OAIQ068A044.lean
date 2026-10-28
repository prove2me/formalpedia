-- Prove2me | Definitions.Def_OAIQ068A044
-- name    : OAIQ068A044
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:21:59.857108+00:00
-- url     : https://prove2.me/theorems/778085ea-cf8b-40a9-a6af-8cab1092f2d7
-- title:
--   Definitions bundle OAIQ068A044 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 27 definitions, 1 instance and 21 theorems. The definitions and types are `OAI.PiExponent.AdmissibleJetPackets.sectionPolynomial`, `OAI.PiExponent.AffineJetCoefficientFrame.polynomialPowerFrame`, `OAI.PiExponent.AffineJetCoefficientFrame.untwistPowerFrame`, `OAI.PiExponent.AffineJetCoefficientInterface.Frame`, `OAI.PiExponent.AffineJetCoefficientInterface.Sections`, `OAI.PiExponent.AffineJetCoefficientInterface.coefficient`, `OAI.PiExponent.AffineJetPolynomial.polynomialCoefficient`, `OAI.PiExponent.CanonicalRecoveryProperties.ComapBijective`, `OAI.PiExponent.CanonicalRecoveryProperties.OrdinaryBijective`, `OAI.PiExponent.ExceptionalAffineChart.idealChartFrame`, `OAI.PiExponent.ExceptionalAffineChart.representedSectionsEquiv`, `OAI.PiExponent.ExceptionalAffineChart.representedSectionsOpaque`, `OAI.PiExponent.ExceptionalAffineChart.sectionsEquiv`, `OAI.PiExponent.ExceptionalAffineChart.sectionsOnOpenEquiv`, `OAI.PiExponent.ExceptionalRepresentedTypes.Frame`, `OAI.PiExponent.ExceptionalRepresentedTypes.Sections`, `OAI.PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped`, `OAI.PiExponent.ExceptionalRepresentedTypes.restrictSections`, `OAI.PiExponent.ExceptionalRepresentedTypes.transportSections`, `OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.ordinaryMap`, `OAI.PiExponent.GeometrySupport.ExceptionalRecoveryMap.twistedMap`, `OAI.PiExponent.GeometrySupport.TwistPresentations.acyclicPresentationOfGenerators`, `OAI.PiExponent.PresentedIdealIso.powerIso`, `OAI.PiExponent.ProjectiveSectionInterface.ofSectionHom`, `OAI.PiExponent.ProjectiveSectionInterface.sectionHom`, `OAI.PiExponent.ReesSheafCechBase.exceptionalPower`, `OAI.PiExponentSeshadri.Geometry.idealPowerSectionsEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalAffineChart`, `PiExponent_Ampleness_ExceptionalAffineChartRestriction`, `PiExponent_Ampleness_ExceptionalPowerPresentation`, `PiExponent_Ampleness_ExceptionalPowerSections`, `PiExponent_Ampleness_ExceptionalRecoveryMap`, `PiExponent_Ampleness_ExceptionalRepresentedOpaque`, `PiExponent_Ampleness_ExceptionalRepresentedTypes`, `PiExponent_Ampleness_ExceptionalTypedRestriction`, `PiExponent_Ampleness_ExceptionalTypedTransport`, `PiExponent_Approximation_TwistPresentations`, `PiExponent_Cohomology_ReesSheafCechBase`, `PiExponent_Geometry_CanonicalRecoveryProperties`, `PiExponent_Geometry_ProjectiveSectionInterface`, `PiExponent_Jets_AdmissibleJetPackets`, `PiExponent_Jets_AffineJetCoefficientFrame`, `PiExponent_Jets_AffineJetCoefficientInterface`, `PiExponent_Jets_AffineJetPolynomial`, `PiExponent_LocalAlgebra_IdealTensorPowers`.
--
--   **Imports.** It imports the bundles `OAIQ068A039`, `OAIQ068A040` and `OAIQ068A041` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A046`; the statements `OAI_PiExponent_AdmissibleJetPackets_formalPackets_surjective_of_jetRestriction`, `OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68`, `OAI_PiExponent_AffineReesCanonicalRecovery_eventually_comap_bijective`, `OAI.PiExponent.AffineReesCanonicalRecovery.eventually_comap_bijective_q68`, `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_affine_recovery`, `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68`, `OAI_PiExponent_GlobalPolynomialWeightedBound_coefficient_bound` and `OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68`; the proofs of `OAI_PiExponentSeshadri_ComponentAmpleDescent_eventual_tensor_cohomology_zero_of_closed_pushforward`, `OAI.PiExponentSeshadri.ComponentAmpleDescent.eventual_tensor_cohomology_zero_of_closed_pushforward_q68`, `OAI_PiExponentSeshadri_Geometry_eventual_twist_ext_zero_of_closed_pushforward`, `OAI.PiExponentSeshadri.Geometry.eventual_twist_ext_zero_of_closed_pushforward_q68`, `OAI_PiExponent_AdmissibleJetPackets_formalPackets_surjective_of_jetRestriction`, `OAI.PiExponent.AdmissibleJetPackets.formalPackets_surjective_of_jetRestriction_q68`, `OAI_PiExponent_BlowupJetSurjectivity_eventual_blowup_jetRestriction_surjective_of_affine_recovery`, `OAI.PiExponent.BlowupJetSurjectivity.eventual_blowup_jetRestriction_surjective_of_affine_recovery_q68`, `OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_power_cohomology_zero`, `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero_q68`, `OAI_PiExponent_GeometrySupport_NoetherianAmpleSerreVanishing_ample_serre_tensor_vanishing`, `OAI.PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_tensor_vanishing_q68`, `OAI_PiExponent_GlobalPolynomialWeightedBound_coefficient_bound`, `OAI.PiExponent.GlobalPolynomialWeightedBound.coefficient_bound_q68`, `OAI_PiExponent_ProjectiveSectionExtension_eventual_projective_pullbackPowerSection_surjective` and `OAI.PiExponent.ProjectiveSectionExtension.eventual_projective_pullbackPowerSection_surjective_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A039
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A041

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealTensorPowers
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma idealPowerInclusion_ideal (J : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) (n : ℕ) :
    Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)
      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)} =
      (Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι})^n := by
  induction n with
  | zero =>
    simp only [idealPowerFrame, idealPowerInclusion]
    exact (congrArg (fun r : Γ(X,U.1) => Ideal.span {r})
      (affineMapCoefficient_id U (Scheme.Modules.restrictUnitIso U.1.ι))).trans (by simp)
  | succ n ih =>
    change Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)} = _
    erw [affineMapCoefficient_comp U _ (idealPowerFrame J U.1 e n),
      ← Ideal.span_singleton_mul_span_singleton,ih]
    rw [show Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))
      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι)} =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} from
        tensor_inclusion_ideal J (J.pow n) ι U e (idealPowerFrame J U.1 e n)]
    rw [pow_succ']

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalPowerSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme}

theorem idealPower_restricted_range (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
      (idealPowerInclusion J ι n) U.1.ι).val.app (.op ⊤)).hom.range =
      (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom := by
  erw [framed_section_range (idealPowerFrame J U.1 e n)]
  have h := idealPowerInclusion_ideal J ι U e n
  rw [← InvertibleLocal.pullback_frame_equation J ι hJ U V hUV, ← Ideal.map_pow] at h
  have h' := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rw [Ideal.map_span, Set.image_singleton] at h'
  simpa only [affineMapCoefficient, U.1.topIso.hom_inv_id_apply,
    PiExponentSeshadri.InvertibleLocal.restrictedInclusion, Category.assoc] using! h'

def idealPowerSectionsEquiv (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    powerSections J n U.1 ≃ₗ[Γ(U.1.toScheme, ⊤)]
      ↥(powerChartIdeal f I n U V hUV) := by
  letI : Mono ι := hJ.1
  letI := idealPowerInclusion_mono J ι n
  let a := PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
    (idealPowerInclusion J ι n) U.1.ι
  have ha : Mono (C := U.1.toScheme.Modules) a :=
    @PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono Y U.1.toScheme
      (J.pow n) (idealPowerInclusion J ι n) U.1.ι inferInstance
      (@idealPowerInclusion_mono Y J ι hJ.1 n)
  have hinj : Function.Injective (a.val.app (.op ⊤)) := by
    let : Mono a.val :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.toPresheafOfModules U.1.toScheme)
        inferInstance _ _ a ha
    exact PresheafOfModules.injective_of_mono a.val (.op ⊤)
  let φ : powerSections J n U.1 →ₗ[Γ(U.1.toScheme, ⊤)]
      Γ(U.1.toScheme, ⊤) := (a.val.app (.op ⊤)).hom
  have hr : φ.range = (powerChartIdeal f I n U V hUV : Submodule Γ(U.1.toScheme, ⊤) _) :=
    idealPower_restricted_range f I J ι hJ n U V hUV e
  exact (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hr)

end PiExponentSeshadri.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))

def sectionsEquiv (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ) :
    ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤) ≃+ ↥((I^n).map φ) :=
  (idealPowerSectionsEquiv f (specIdeal I) L ι hL n (chartOpen j)
    ⟨⊤, isAffineOpen_top _⟩ (by simp) e).toAddEquiv |>.trans
      ((idealMapAddEquiv (chartFunctionsEquiv j) (chartPowerIdeal I f j n)).trans
        ((LinearEquiv.ofEq _ _ (map_chartPowerIdeal I f j φ hf n)).toAddEquiv))

theorem sectionsEquiv_apply (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme) (n : ℕ)
    (s : ((L.pow n).sheaf.restrict (chartOpen j).1.ι).val.obj (.op ⊤)) :
    (sectionsEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j
        ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (L.pow n)
          (idealPowerInclusion L ι n) (chartOpen j).1.ι).val.app (.op ⊤) s) := rfl

def idealChartFrame (L : Y.IdealSheafData)
    (r : Γ(Spec (CommRingCat.of A), ⊤))
    (hprincipal : (L.comap j).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    (PiExponentSeshadri.IdealModule.closedModule L).restrict (chartOpen j).1.ι ≅
      O (chartOpen j).1.toScheme :=
  PiExponentSeshadri.IdealModule.frameOnRange _ j
    (PiExponentSeshadri.IdealModule.frame_restriction L j r hprincipal hregular).some

end PiExponent.ExceptionalAffineChart
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalAffineChartRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.RestrictionCohomology
open PiExponentSeshadri.IdealPullback


section Functions
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

lemma chartFunctions_naturality (s : Γ(j.opensRange.toScheme,⊤)) :
    chartFunctionsEquiv j' ((Y.homOfLE (opensRange_le j j' θ h)).appTop s) =
      θ (chartFunctionsEquiv j s) := by
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      (j'.isoOpensRange.hom.appTop ((Y.homOfLE (opensRange_le j j' θ h)).appTop s)) =
    θ ((Scheme.ΓSpecIso (CommRingCat.of A)).hom (j.isoOpensRange.hom.appTop s))
  have hc := congrArg (fun g => g.appTop) (chart_square j j' θ h)
  simp only [Scheme.Hom.comp_appTop] at hc
  have he : (Y.homOfLE (opensRange_le j j' θ h)).appTop ≫
        j'.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom =
      j.isoOpensRange.hom.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom θ := by
    rw [← Category.assoc, hc, Category.assoc, Scheme.ΓSpecIso_naturality]
  exact CategoryTheory.congr_fun he s

lemma functionsOnOpenEquiv_naturality (s : Γ(Y,j.opensRange)) :
    functionsOnOpenEquiv j' (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
      θ (functionsOnOpenEquiv j s) := by
  change chartFunctionsEquiv j' (j'.opensRange.topIso.inv
    (Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)) =
      θ (chartFunctionsEquiv j (j.opensRange.topIso.inv s))
  rw [topIso_restriction]
  exact chartFunctions_naturality j j' θ h _

end Functions

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

theorem restrictedInclusion_value (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
    (U : Y.Opens) (s : Γ(L.sheaf, U)) :
    (PiExponentSeshadri.InvertibleLocal.restrictedInclusion L ι U.ι).app ⊤
      ((restrictionSectionsIso U L.sheaf).inv s) = U.topIso.inv (ι.app U s) := by
  change (U.ι.appIso ⊤).hom
    (ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s)) = _
  rw [Scheme.Opens.ι_appIso]
  change ι.app (U.ι ''ᵁ ⊤) (L.sheaf.presheaf.map (eqToHom U.ι_image_top).op s) =
    Y.presheaf.map (eqToHom U.ι_image_top).op (ι.app U s)
  exact CategoryTheory.congr_fun (ι.mapPresheaf.naturality (eqToHom U.ι_image_top).op) s

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

def sectionsOnOpenEquiv (n : ℕ) :
    Γ((L.pow n).sheaf, j.opensRange) ≃+ ↥((I^n).map φ) :=
  (restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).addCommGroupIsoToAddEquiv.symm.trans
    (sectionsEquiv I f j φ hf L ι hL e n)

theorem sectionsOnOpenEquiv_apply (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val =
      chartFunctionsEquiv j ((chartOpen j).1.topIso.inv
        ((idealPowerInclusion L ι n).app j.opensRange s)) := by
  change (sectionsEquiv I f j φ hf L ι hL e n
    ((restrictionSectionsIso (chartOpen j).1 (L.pow n).sheaf).inv s)).val = _
  erw [sectionsEquiv_apply]
  exact congrArg (chartFunctionsEquiv j)
    (restrictedInclusion_value (L.pow n) (idealPowerInclusion L ι n) (chartOpen j).1 s)

def representedSectionsEquiv (n : ℕ) :
    (schemeFreeOpen_p0 Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  ({ freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j.opensRange with
      map_add' := fun _ _ => rfl } :
      (schemeFreeOpen_p0 Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
        Γ((L.pow n).sheaf, j.opensRange)).trans
    (sectionsOnOpenEquiv I f j φ hf L ι hL e n)

variable {B : Type} [CommRing B]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : L.sheaf.restrict (chartOpen j').1.ι ≅ O (chartOpen j').1.toScheme)

theorem sectionsOnOpenEquiv_restrict (n : ℕ) (s : Γ((L.pow n).sheaf, j.opensRange)) :
    (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s)).val =
      θ (sectionsOnOpenEquiv I f j φ hf L ι hL e n s).val := by
  rw [sectionsOnOpenEquiv_apply, sectionsOnOpenEquiv_apply]
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion L ι n).mapPresheaf.naturality
      (homOfLE (opensRange_le j j' θ h)).op) s
  change (idealPowerInclusion L ι n).app j'.opensRange
      ((L.pow n).sheaf.presheaf.map (homOfLE (opensRange_le j j' θ h)).op s) =
    Y.presheaf.map (homOfLE (opensRange_le j j' θ h)).op
      ((idealPowerInclusion L ι n).app j.opensRange s) at hn
  rw [hn]
  exact functionsOnOpenEquiv_naturality j j' θ h _

theorem representedSectionsEquiv_restrict (n : ℕ)
    (s : schemeFreeOpen_p0 Y j.opensRange ⟶ (L.pow n).sheaf) :
    (representedSectionsEquiv I f j' φ' hf' L ι hL e' n
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s)).val =
      θ (representedSectionsEquiv I f j φ hf L ι hL e n s).val := by
  change (sectionsOnOpenEquiv I f j' φ' hf' L ι hL e' n
    (freeOpenEquiv Y.ringCatSheaf (L.pow n).sheaf j'.opensRange
      (freeOpenMap Y.ringCatSheaf (homOfLE (opensRange_le j j' θ h)) ≫ s))).val = _
  erw [freeOpenEquiv_naturality]
  exact sectionsOnOpenEquiv_restrict I f j φ hf L ι hL e j' θ h φ' hf' e' n _

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalPowerPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectionFormula.unit_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PresentedIdealIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem imageIdealSheaf_idealPowerInclusion
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) (n : ℕ)
    [J.sheaf.IsQuasicoherent] [(J.pow n).sheaf.IsQuasicoherent] :
    imageIdealSheaf (idealPowerInclusion J ι n) = (imageIdealSheaf ι)^n := by
  classical
  have hlocal (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
    obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
    exact ⟨⟨U,hU⟩,hyU,⟨restrictOpenFrame hUV e⟩⟩
  choose U hy he using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let e := Classical.choice (he y)
    rw [Scheme.IdealSheafData.ideal_pow]
    change (imageIdealSheaf (idealPowerInclusion J ι n)).ideal (U y) =
      ((imageIdealSheaf ι).ideal (U y))^n
    erw [imageIdealSheaf_on_frame (idealPowerInclusion J ι n) (U y)
        (idealPowerFrame J (U y).1 e n),
      imageIdealSheaf_on_frame ι (U y) e]
    exact idealPowerInclusion_ideal J ι (U y) e n

theorem idealPower_presents
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    PresentsPullbackIdeal (I^n) f (J.pow n) (idealPowerInclusion J ι n) := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (J.pow n)
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  let : (J.pow n).sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (J.pow n).sheaf).choose.isQuasicoherent
  let : Mono ι := hJ.1
  refine ⟨@idealPowerInclusion_mono Y J ι hJ.1 n, ?_⟩
  intro U V hUV
  have h := imageIdealSheaf_idealPowerInclusion J ι n
  rw [imageIdealSheaf_eq_comap I f J ι hJ,
    ← PiExponentSeshadri.IdealPullback.comap_pow] at h
  have hu := congrArg (fun K : Y.IdealSheafData => K.ideal U) h
  exact hu.trans (PiExponentSeshadri.IdealPullback.comap_ideal (I^n) f U V hUV)

def powerIso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (J.pow n).sheaf ≅ closedModule ((I^n).comap f) :=
  @asIso Y.Modules _ _ _
    (toIdealModule (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))
    (toIdealModule_isIso (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))

@[reassoc (attr := simp)] theorem powerIso_hom_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (powerIso I f J ι hJ n).hom ≫ closedInclusion ((I^n).comap f) =
      idealPowerInclusion J ι n :=
  toIdealModule_inclusion (I^n) f (J.pow n) (idealPowerInclusion J ι n)
    (idealPower_presents I f J ι hJ n)

end PiExponent.PresentedIdealIso

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalRecoveryMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

def ordinaryMap (n : ℕ) : closedModule (I^n) ⟶
    (Scheme.Modules.pushforward f).obj (modulePow Y E.sheaf n) :=
  IdealPullbackMap.comap f (I^n) ≫
    (Scheme.Modules.pushforward f).map (PresentedIdealIso.powerIso I f E ι hE n).inv

@[reassoc (attr := simp)] theorem ordinaryMap_inclusion (n : ℕ) :
    ordinaryMap f I E ι hE n ≫
      (Scheme.Modules.pushforward f).map (idealPowerInclusion E ι n) =
    closedInclusion (I^n) ≫ structureMap f := by
  have he : (PresentedIdealIso.powerIso I f E ι hE n).inv ≫
      idealPowerInclusion E ι n = closedInclusion ((I^n).comap f) := by
    rw [← PresentedIdealIso.powerIso_hom_inclusion I f E ι hE n]
    exact Iso.inv_hom_id_assoc _ _
  rw [ordinaryMap, Category.assoc]
  erw [← Functor.map_comp, he]
  exact IdealPullbackMap.comap_inclusion f (I^n)

def twistedMap (A : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor A n).obj (closedModule (I^n)) ⟶
      (Scheme.Modules.pushforward f).obj ((E.tensor (A.pullback f)).pow n).sheaf :=
  (moduleTwistFunctor A n).map (ordinaryMap f I E ι hE n) ≫
    (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).inv ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n).hom ≫
          (lineTensorPow E (A.pullback f) n).inv)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalRepresentedOpaque
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalAffineChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback

variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}
variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : L.sheaf.restrict (chartOpen j).1.ι ≅ O (chartOpen j).1.toScheme)

theorem exists_representedSectionsOpaque (n : ℕ) :
    ∃ E : (schemeFreeOpen_p1 Y j.opensRange ⟶ (L.pow n).sheaf) ≃+
      ↥((I^n).map φ), E = representedSectionsEquiv I f j φ hf L ι hL e n :=
  ⟨_, rfl⟩

def representedSectionsOpaque (n : ℕ) :
    (schemeFreeOpen_p1 Y j.opensRange ⟶ (L.pow n).sheaf) ≃+ ↥((I^n).map φ) :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose

theorem representedSectionsOpaque_eq (n : ℕ) :
    representedSectionsOpaque I f j φ hf L ι hL e n =
      representedSectionsEquiv I f j φ hf L ι hL e n :=
  (exists_representedSectionsOpaque I f j φ hf L ι hL e n).choose_spec

theorem representedSectionsOpaque_apply (n : ℕ)
    (b : schemeFreeOpen_p1 Y j.opensRange ⟶ (L.pow n).sheaf) :
    representedSectionsOpaque I f j φ hf L ι hL e n b =
      representedSectionsEquiv I f j φ hf L ι hL e n b :=
  congrArg (fun E => E b) (representedSectionsOpaque_eq I f j φ hf L ι hL e n)

end
end PiExponent.ExceptionalAffineChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalRepresentedTypes
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A : Type} [CommRing R] [CommRing A] {Y : Scheme}

def Frame (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) : Type :=
  L.sheaf.restrict (ExceptionalAffineChart.chartOpen j).1.ι ≅
    O (ExceptionalAffineChart.chartOpen j).1.toScheme

def Sections (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : Type :=
  freeOpen Y.ringCatSheaf j.opensRange ⟶ (L.pow n).sheaf

instance instAddCommGroupSections (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
    (L : LineBundle Y) (n : ℕ) : AddCommGroup (Sections j L n) :=
  Preadditive.homGroup (C := Y.Modules)
    (freeOpen Y.ringCatSheaf j.opensRange) (L.pow n).sheaf

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)

def representedSectionsTyped (n : ℕ) : Sections j L n ≃+ ↥((I^n).map φ) :=
  ExceptionalAffineChart.representedSectionsOpaque I f j φ hf L ι hL e n

theorem representedSectionsTyped_apply (n : ℕ) (b : Sections j L n) :
    representedSectionsTyped I f j φ hf L ι hL e n b =
      ExceptionalAffineChart.representedSectionsEquiv I f j φ hf L ι hL e n b :=
  ExceptionalAffineChart.representedSectionsOpaque_apply I f j φ hf L ι hL e n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalTypedRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

def restrictSections (L : LineBundle Y) (n : ℕ) :
    Sections j L n →+ Sections j' L n where
  toFun b := freeOpenMap Y.ringCatSheaf
    (homOfLE (ExceptionalAffineChart.opensRange_le j j' θ h)) ≫ b
  map_zero' := Limits.HasZeroMorphisms.comp_zero (C := Y.Modules) _ _
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : Frame j' L)

theorem representedSectionsTyped_restrict (n : ℕ) (b : Sections j L n) :
    (representedSectionsTyped I f j' φ' hf' L ι hL e' n
      (restrictSections j j' θ h L n b)).val =
      θ (representedSectionsTyped I f j φ hf L ι hL e n b).val := by
  rw [representedSectionsTyped_apply, representedSectionsTyped_apply]
  exact ExceptionalAffineChart.representedSectionsEquiv_restrict
    I f j φ hf L ι hL e j' θ h φ' hf' e' n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalTypedTransport
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.framedSectionsMorphism_proper _root_.OAI.PiExponentSeshadri.Projective.sectionsMorphism_proper _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.TensorPure.tensorSection_isIso _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque

variable {A : Type} [CommRing A] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (L : LineBundle Y)

theorem frame_nonempty_of_open {U : Y.Opens} (h : U = j.opensRange)
    (he : Nonempty (L.sheaf.restrict U.ι ≅ O U.toScheme)) :
    Nonempty (Frame j L) := by
  subst U
  exact he

def transportSections (n : ℕ) {V : Y.Opens} (h : j.opensRange = V) :
    (schemeFreeOpen Y V ⟶ (L.pow n).sheaf) ≃+ Sections j L n where
  toFun b := freeOpenMap Y.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap Y.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  right_inv b := by
    subst V
    simp [freeOpenMap]
    exact (Category.id_comp _).trans (Category.id_comp b)
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistPresentations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.PullbackTensor.line_isIso _root_.OAI.PiExponentSeshadri.PullbackTensor.power_step_isIso _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.TwistPresentations
noncomputable section
universe w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

variable (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections)

theorem presentation_shortExact (n : ℕ) :
    (ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n)).ShortExact := by
  have : Epi s.π := s.epi
  have hbase : (ShortComplex.kernelSequence (C := X.Modules) s.π).ShortExact := {
    exact := ShortComplex.kernelSequence_exact s.π
    mono_f := equalizer.ι_mono (C := X.Modules) (f := s.π)
    epi_g := s.epi }
  have : Functor.PreservesZeroMorphisms (C := X.Modules) (D := X.Modules)
      (moduleTwistFunctor L n) := inferInstance
  let T := (ShortComplex.kernelSequence (C := X.Modules) s.π).map (moduleTwistFunctor L n)
  let e : T ≅ ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (twistShiftIso L M n0 n)
      (by
        simp only [presentationLeft]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        simp only [presentationRight]
        exact Category.id_comp _)
  exact ShortComplex.shortExact_of_iso e (moduleTwistFunctor_shortExact L n _ hbase)

def acyclicPresentationOfGenerators [IsLocallyNoetherian X] [HasExt.{w} X.Modules]
    (L : LineBundle X) (M : {M : X.Modules // M.IsFinitePresentation}) (n0 : ℕ)
    (s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections) [s.IsFiniteType]
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{w} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0) :
    SerreDimensionShift.AcyclicPresentation.{w} (C := X.Modules) (schemeUnit X)
      (coherentTwistFamily L) M := by
  have : M.val.IsFinitePresentation := M.property
  exact {
    kernel := ⟨presentationKernel L s, presentationKernel_isFinitePresentation L s⟩
    shift := n0
    middle := presentationMiddle L s
    left := presentationLeft L s
    right := presentationRight L s
    comp_zero := presentation_comp_zero L s
    shortExact := presentation_shortExact L s
    acyclic := presentationMiddle_ext_zero L s (schemeUnit X) hpow }

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectionFormula.line_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isIntegral _root_.OAI.PiExponentSeshadri.ReesGrading.affineBlowup_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev exceptionalPower (n : ℕ) := ((exceptionalLineBundle I).pow n).sheaf

end
end PiExponent.ReesSheafCechBase

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CanonicalRecoveryProperties
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CanonicalRecoveryProperties
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open GeometrySupport

def ComapBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (U : X.Opens) : Prop :=
  Function.Bijective ((IdealPullbackMap.comap f I).app U)

def OrdinaryBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) : Prop :=
  Function.Bijective ((ExceptionalRecoveryMap.ordinaryMap f I E ι hE n).app U)

end PiExponent.CanonicalRecoveryProperties

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetPolynomial
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
open PiExponent.ExceptionalAffineChart
open PiExponentSeshadri.IdealPullback
variable {X : Scheme} {R : Type} [CommRing R]

def polynomialCoefficient (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : R :=
  functionsOnOpenEquiv j (globalSectionCoefficient A n (chartOpen j) e s)

end PiExponent.AffineJetPolynomial
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetCoefficientInterface
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientInterface
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.ExceptionalAffineChart
variable {X : Scheme} {R : Type} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (A : LineBundle X)

def Frame : Type := A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme

def Sections (n : ℕ) : Type := GlobalSections X (modulePow X A.sheaf n)

def coefficient (n : ℕ) (e : Frame j A) : Sections A n → R :=
  AffineJetPolynomial.polynomialCoefficient j A n e

end PiExponent.AffineJetCoefficientInterface
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionInterface
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSectionInterface
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.AffineJetCoefficientInterface

variable {X Y : Scheme.{0}}

def sectionHom (L : LineBundle X) (n : ℕ) :
    Sections L n → GlobalSections X (modulePow X L.sheaf n) := fun s => s

def ofSectionHom (L : LineBundle X) (n : ℕ) :
    GlobalSections X (modulePow X L.sheaf n) → Sections L n := fun s => s

@[simp]
theorem sectionHom_ofSectionHom (L : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X L.sheaf n)) :
    sectionHom L n (ofSectionHom L n s) = s := rfl

attribute [local irreducible] AffineJetCoefficientInterface.Frame
  AffineJetCoefficientInterface.Sections

end
end PiExponent.ProjectiveSectionInterface

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AdmissibleJetPackets
attribute [-instance] _root_.OAI.PiExponent.AdmissibleCurveImage.projection_restrict_isIso _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleJetPackets
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.AdmissibleBlowupGeometry
open PiExponent.BlowupJetSurjectivity PiExponent.ExceptionalAffineChart
attribute [local irreducible] AdmissibleBlowupGeometry.affineChart AdmissibleBlowupGeometry.hyperplane
  AdmissibleBlowupGeometry.centerIdeal
  AffineJetCoefficientInterface.Frame AffineJetCoefficientInterface.Sections
  AffineJetCoefficientInterface.coefficient
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def sectionPolynomial (n : ℕ)
    (e : AffineJetCoefficientInterface.Frame (affineChart d) (hyperplane d)) :
    AffineJetCoefficientInterface.Sections (hyperplane d) n → PiExponentApprox.FramePolynomial d.m :=
  AffineJetCoefficientInterface.coefficient (affineChart d) (hyperplane d) n e

end PiExponent.AdmissibleJetPackets
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetCoefficientFrame
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ExceptionalRepresentedTypes.instAddCommGroupSections _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientFrame
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.AffineJetSupport PiExponent.AffineJetQuotient
variable {X : Scheme}

def untwistPowerFrame (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X A.sheaf n).restrict U.ι ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTwistUnitIso A n).symm ≪≫
    (moduleTwistRestrictFrame A U e n).app (structureSheaf X) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

open PiExponent.ExceptionalAffineChart PiExponent.AffineJetPolynomial
variable {R : Type} [CommRing R]

def polynomialPowerFrame (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (A : LineBundle X) (n : ℕ)
    (e : A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme) :
    (modulePow X A.sheaf n).restrict j ≅ O (Spec (CommRingCat.of R)) :=
  (Scheme.Modules.restrictFunctorCongr j.isoOpensRange_hom_ι.symm).app _ ≪≫
    (Scheme.Modules.restrictFunctorComp j.isoOpensRange.hom j.opensRange.ι).app _ ≪≫
    restrictFrame j.isoOpensRange.hom (untwistPowerFrame A (chartOpen j).1 e n)

end PiExponent.AffineJetCoefficientFrame
end

end OAI
end


