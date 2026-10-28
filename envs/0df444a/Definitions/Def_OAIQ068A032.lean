-- Prove2me | Definitions.Def_OAIQ068A032
-- name    : OAIQ068A032
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:09:23.5353+00:00
-- url     : https://prove2.me/theorems/79b34f86-018c-428e-a1bf-1c3a24ceb2b5
-- title:
--   Definitions bundle OAIQ068A032 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 60 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure, 1 instance and 30 theorems. The definitions and types are `OAI.PiExponent.AdmissibleMatrixInterpolation.WeightedPolynomials`, `OAI.PiExponent.AdmissibleMatrixInterpolation.packetMap`, `OAI.PiExponent.AffineJetQuotient.globalSectionCoefficient`, `OAI.PiExponent.AffineJetQuotient.untwistSectionsIso`, `OAI.PiExponent.AffineJetSupport.globalQuotientValue`, `OAI.PiExponent.AffineJetSupport.localQuotientEquiv`, `OAI.PiExponent.BlowupJetSurjectivity.jetRestriction`, `OAI.PiExponent.BlowupJetSurjectivity.twistedIdeal`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveAffineOpens`, `OAI.PiExponent.CurveNormalizationModel.parameterCurveUnit`, `OAI.PiExponent.GeneratorsSectionCover.generatorSection`, `OAI.PiExponent.GeometrySupport.CechH1Transfer.SectionComparison`, `OAI.PiExponent.GeometrySupport.CechH1Transfer.freeOpenHomAddCommGroup`, `OAI.PiExponent.GeometrySupport.CechH1Transfer.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity.coordinateLineBundle`, `OAI.PiExponent.GeometrySupport.ProjectiveTupleCharts.coordinateTupleCoefficient`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.comparison`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.restrictEquiv`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.sectionMap`, `OAI.PiExponent.GeometrySupport.PushforwardOpenSections.tupleSectionMap`, `OAI.PiExponent.GeometrySupport.SerrePowerDescent.moduleTwistLineIso`, `OAI.PiExponentSeshadri.FiniteSupport.pointFrame`, `OAI.PiExponentSeshadri.FiniteSupport.pushforwardUnitSections`, `OAI.PiExponentSeshadri.Geometry.overFrame`, `OAI.PiExponentSeshadri.Geometry.powerSections`, `OAI.PiExponentSeshadri.Geometry.restrictedPullbackFrame`, `OAI.PiExponentSeshadri.Projective.coordinatePullbackFrame`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_BlowupJetSurjectivity`, `PiExponent_Ampleness_ExceptionalPowerSections`, `PiExponent_Approximation_AdmissibleMatrixInterpolation`, `PiExponent_Approximation_GeneratorsSectionCover`, `PiExponent_Approximation_IntegralLineSections`, `PiExponent_Approximation_PushforwardOpenSections`, `PiExponent_Approximation_PushforwardSectionComparison`, `PiExponent_Approximation_SerrePowerDescent`, `PiExponent_Cohomology_CechH1Transfer`, `PiExponent_Cohomology_CurveNormalizationCohomology`, `PiExponent_Cohomology_FiniteLineEuler`, `PiExponent_Cohomology_FiniteSupportCohomology`, `PiExponent_Cohomology_ProjectiveCoordinateAcyclicity`, `PiExponent_Geometry_CartierSequence`, `PiExponent_Geometry_CurveEffectiveTwist`, `PiExponent_Geometry_CurveModelFieldEmbedding`, `PiExponent_Geometry_PlaceCenteredBranch`, `PiExponent_Geometry_ProjectiveCoordinateFiniteSections`, `PiExponent_Geometry_ProjectiveCoordinatePullback`, `PiExponent_Geometry_ProjectivePullbackFrames`, `PiExponent_Geometry_ProjectiveTupleCharts`, `PiExponent_Jets_AffineJetQuotient`, `PiExponent_Jets_AffineJetSupport`, `PiExponent_Jets_JetCenterIdentification`, `PiExponent_Polynomials_WeightedMonomialPole`.
--
--   **Imports.** It imports the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024` and `OAIQ068A025` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A038` and `OAIQ068A039`; the statements `OAI_PiExponent_AdmissibleMatrixInterpolation_eventual_packets_of_eventual_jetRestriction`, `OAI.PiExponent.AdmissibleMatrixInterpolation.eventual_packets_of_eventual_jetRestriction_q68`, `OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation_of_eventual_jetRestriction` and `OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation_of_eventual_jetRestriction_q68`; the proofs of `OAI_PiExponent_CurveDerivativeVanishing_logarithmic_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.logarithmic_words_vanish_q68`, `OAI_PiExponent_CurveDerivativeVanishing_ordinary_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.ordinary_words_vanish_q68`, `OAI_PiExponent_CurveInequality_no_fibre_excess_of_constant_coordinate` and `OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A020
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022
import Definitions.Def_OAIQ068A023
import Definitions.Def_OAIQ068A024
import Definitions.Def_OAIQ068A025

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_IntegralLineSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

variable [IsIntegral X]

theorem LineBundle.noZeroSMulDivisors (L : LineBundle X)
    (U : X.Opens) [Nonempty U] : NoZeroSMulDivisors Γ(X, U) Γ(L.sheaf, U) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a m} h := by
    obtain ⟨x, hx⟩ := ‹Nonempty U›
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
    let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
    have : Nonempty V := ⟨⟨⟨x, hxT⟩, hx⟩⟩
    have : Nonempty T := ⟨⟨x, hxT⟩⟩
    let W : X.Opens := T.ι ''ᵁ V
    have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
    let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
    let ar : Γ(X, W) := X.presheaf.map i.op a
    let mr : Γ(L.sheaf, W) := L.sheaf.presheaf.map i.op m
    have hr : ar • mr = 0 := by
      have hh := congrArg (fun z => L.sheaf.presheaf.map i.op z) h
      simpa only [L.sheaf.map_smul, map_zero] using hh
    let ar' : Γ(T.toScheme, V) := (T.ι.appIso V).hom ar
    let mr' : Γ(L.sheaf.restrict T.ι, V) := (L.sheaf.restrictAppIso T.ι V).inv mr
    let cr : Γ(T.toScheme, V) := e.hom.app V mr'
    have hr' : ar' • mr' = 0 := by
      rw [← Scheme.Modules.smul_restrictAppIso_inv_apply]
      simp only [hr, map_zero]
    have hmul : ar' * cr = 0 := by
      have hh := e.hom.app_smul (r := ar') (x := mr')
      change e.hom.app V (ar' • mr') = ar' * cr at hh
      rw [hr', map_zero] at hh
      exact hh.symm
    rcases mul_eq_zero.mp hmul with ha | hm
    · left
      apply map_injective_of_isIntegral X i
      have hinj := (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).hom).injective
      apply hinj
      simpa only [map_zero] using ha
    · right
      apply L.restriction_injective i
      have hinj := (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
      apply (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective
      apply hinj
      change cr = e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv
        (L.sheaf.presheaf.map i.op 0))
      refine hm.trans ?_
      simp only [map_zero]
      rfl

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SerrePowerDescent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.SerrePowerDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

def moduleTwistLineIso {L N : LineBundle X} (e : L.sheaf ≅ N.sheaf) (M : X.Modules) :
    ∀ n : ℕ, (moduleTwistFunctor L n).obj M ≅ (moduleTwistFunctor N n).obj M
  | 0 => Iso.refl M
  | n + 1 => moduleTensorIso (moduleTwistLineIso e M n) e

end
end PiExponent.GeometrySupport.SerrePowerDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFiniteSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M))

variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

variable [Fintype σ]

lemma coordinatePowerOverlap_injective (n : ℕ) (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinatePowerOverlap M s k hc f hf n i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinatePowerOverlap_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (b : schemeFreeOpen_p1 X (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) :
    RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i))))
      (coordinatePowerOverlap M s k hc f hf n i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

lemma coordinatePowerOverlap_surjective_regular (n : ℕ) (i : σ) (a : Finset (ChartVariables i))
    (p : Laurent σ K n)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (a : Set (ChartVariables i)))) p) :
    ∃ b, coordinatePowerOverlap M s k hc f hf n i a b = p :=
  framedLaurentOverlap_surjective_regular _ _ _ _ _ _ _ p hp

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectivePullbackFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

def restrictedPullbackFrame (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (g : V.toScheme ⟶ U.toScheme) (h : V.ι ≫ f = g ≫ U.ι)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pullback f).obj M).restrict V.ι ≅ O V.toScheme :=
  (exists_restricted_pullback_frame_all_of_factor f U V g h e).choose

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinatePullback
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinatePullbackFrame (i : σ) :
    (coordinatePullbackModule k s hc).restrict (SectionOpens.isoOpen (s i)).ι ≅
      O (SectionOpens.isoOpen (s i)).toScheme :=
  restrictedPullbackFrame (sectionsMorphism k s hc)
    (PiExponent.ProjectiveO1.coordinateOpen i) (SectionOpens.isoOpen (s i))
    (coordinateChartMap k s hc i) (coordinateChartMap_factor k s hc i).symm
    (LineBundleGluing.openFrame PiExponent.ProjectiveO1.coordinateCocycle i
      (PiExponent.ProjectiveO1.coordinateOpen i) le_rfl)

attribute [local irreducible] coordinatePullbackModule coordinatePullbackFrame coordinatePullbackSection

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveTupleCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M))
variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

attribute [local irreducible] coordinatePowerOverlap modulePow

def coordinateTupleCoefficient (n q : ℕ) (t : Fin (q + 1) → σ) :
    (schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) →+ Laurent σ K n :=
  (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

theorem coordinateTupleCoefficient_injective (n q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateTupleCoefficient M s k hc f hf n q t) :=
  (coordinatePowerOverlap_injective M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).injective

theorem coordinateTupleCoefficient_regular (n q : ℕ) (t : Fin (q + 1) → σ)
    (b : schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) :
    RegularOn (Set.range t) (coordinateTupleCoefficient M s k hc f hf n q t b) := by
  have h := coordinatePowerOverlap_regular M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0) b)
  unfold coordinateTupleCoefficient
  change RegularOn (Set.range t) ((coordinatePowerOverlap M s k hc f hf n (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

theorem coordinateTupleCoefficient_surjective_regular (n q : ℕ)
    (t : Fin (q + 1) → σ) (p : Laurent σ K n) (hp : RegularOn (Set.range t) p) :
    ∃ b, coordinateTupleCoefficient M s k hc f hf n q t b = p := by
  obtain ⟨b, hb⟩ := coordinatePowerOverlap_surjective_regular M s k hc f hf n (t 0)
    (tupleVariables t 0) p (by simpa only [tupleVariables_support] using hp)
  refine ⟨(freeOpenHomCongr (modulePow X M n)
    (coordinateFiniteOpen_tuple M s t 0)).symm b, ?_⟩
  change (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0))
    ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0))
      ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).symm b)) = p
  rw [AddEquiv.apply_symm_apply]
  exact hb

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveCoordinateAcyclicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
attribute [local irreducible] coordinatePowerOverlap modulePow

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

def coordinateLineBundle : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hc]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨PiExponentSeshadri.SectionOpens.isoOpen (s i), hi, ⟨sectionFrame (s i)⟩⟩

end
end PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechH1Transfer
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

abbrev schemeFreeOpen (Z : Scheme.{u}) (U : Z.Opens) : Z.Modules :=
  freeOpen Z.ringCatSheaf U

@[instance_reducible] def freeOpenHomAddCommGroup
    (Z : Scheme.{u}) (U : Z.Opens) (M : Z.Modules) :
    AddCommGroup (freeOpen Z.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen Z U ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

structure SectionComparison (U : J → X.Opens) (V : J → Y.Opens)
    (M : X.Modules) (N : Y.Modules) where
  vertex : ∀ t : Fin 1 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) ≃+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair : ∀ t : Fin 2 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  triple : ∀ t : Fin 3 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair_injective : ∀ t, Function.Injective (pair t)
  pair_restrict : ∀ (t : Fin 2 → J) (k : Fin 2) b,
    pair t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (vertex (t ∘ k.succAbove) b)
  triple_restrict : ∀ (t : Fin 3 → J) (k : Fin 3) b,
    triple t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (pair (t ∘ k.succAbove) b)

end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupJetSurjectivity
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport

variable {X B : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def twistedIdeal (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor A n).obj (PiExponentSeshadri.IdealModule.closedModule (I ^ n))

def jetRestriction (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (s : GlobalSections X (modulePow X A.sheaf n)) :
    GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient (I ^ n))) :=
  s ≫ (moduleTwistUnitIso A n).inv ≫
    (moduleTwistFunctor A n).map (PiExponentSeshadri.IdealModule.structureMap (I ^ n).subschemeι)

end
end PiExponent.BlowupJetSurjectivity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalPowerSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

lemma InvertibleLocal.pullback_frame_equation {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    (I.ideal V).map (f.appLE V.1 U.1 hUV).hom =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← PiExponentSeshadri.InvertibleLocal.restricted_image_on_chart J ι hJ U.1.ι
        ⟨⊤,isAffineOpen_top _⟩ V (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
    ext r
    change (∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤) s = r) ↔
      ∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤)
        (e.inv.val.app (.op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (.op ⊤) s,?_⟩
      have ht : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (.op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩; exact ⟨e.inv.val.app (.op ⊤) s,hs⟩
  rw [IdealPullback.comap_ι_top,IdealPullback.comap_ideal I f U V hUV] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

abbrev powerSections (J : LineBundle Y) (n : ℕ) (U : Y.Opens) :
    ModuleCat Γ(U.toScheme, ⊤) := ((J.pow n).sheaf.restrict U.ι).val.obj (.op ⊤)

end PiExponentSeshadri.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem lift_residue (z : ι → E) (c : ι → ℂ) (hc : Centered z c p) (i : ι) :
    CurveLocalOrder.residueAugmentation ℂ (ring p) (lift p z c hc i) = c i := by
  have hm : lift p z c hc i - algebraMap ℂ (ring p) (c i) ∈
      IsLocalRing.maximalIdeal (ring p) := by
    apply p.valuation.toValuation.mem_maximalIdeal_iff.mpr
    exact hc i
  have hz : CurveLocalOrder.residueAugmentation ℂ (ring p)
      (lift p z c hc i - algebraMap ℂ (ring p) (c i)) = 0 := by
    change (CurveLocalOrder.residueCoefficientEquiv ℂ (ring p)).symm
      (IsLocalRing.residue (ring p) _) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero]
  rw [map_sub, CurveLocalOrder.residueAugmentation_algebraMap, sub_eq_zero] at hz
  exact hz

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AdmissibleMatrixInterpolation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleMatrixInterpolation
open Filter
open DeterminantContradiction AdmissibleBlowupGeometry
variable {ν : ℝ} (d : FixedData ν)

def WeightedPolynomials (n : ℕ) :=
  {P : PiExponentApprox.FramePolynomial d.m //
    WeightedSliceDegree.SupportBound (fun i => (d.curveDegreeWeights i : ℝ))
      ((n : ℝ) * (scale d).radius) P}

def packetMap (n : ℕ) (P : WeightedPolynomials d n) :=
  fun j : Fin d.K => JetGeometry.rationalCoefficientPacket d.curveJetWeights
    ((n : ℚ) * (scale d).radius) (FormalLogJet.formalJet (d.curveCenters j) P.val)

end PiExponent.AdmissibleMatrixInterpolation

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GeneratorsSectionCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeneratorsSectionCover
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def generatorSection (L : LineBundle X) (G : L.sheaf.GeneratingSections) (i : G.I) :
    GlobalSections X L.sheaf := schemeInclusion i ≫ G.π

end
end PiExponent.GeneratorsSectionCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PushforwardOpenSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.ProjectiveChartSections
open CechOne CechHigher

abbrev schemeFreeOpen_p0 (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)

def sectionMap (U : X.Opens) :
    (schemeFreeOpen_p0 X U ⟶ M) →+
      (schemeFreeOpen_p0 Y (f ⁻¹ᵁ U) ⟶ N) where
  toFun b := (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
    (β.app U (freeOpenAddEquiv U M b))
  map_zero' := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M 0)) = 0
    rw [_root_.map_zero, _root_.map_zero]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_zero
  map_add' b c := by
    change (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm
      ((β.app U).hom (freeOpenAddEquiv U M (b + c))) = _
    rw [_root_.map_add, _root_.map_add]
    exact (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.map_add _ _

@[simp] theorem sectionMap_value (U : X.Opens) (b : schemeFreeOpen_p0 X U ⟶ M) :
    freeOpenAddEquiv (f ⁻¹ᵁ U) N (sectionMap f β U b) =
      β.app U (freeOpenAddEquiv U M b) := AddEquiv.apply_symm_apply _ _

theorem sectionMap_bijective (U : X.Opens) (h : Function.Bijective (β.app U)) :
    Function.Bijective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.bijective.comp
    (h.comp (freeOpenAddEquiv U M).bijective)

theorem sectionMap_injective (U : X.Opens) (h : Function.Injective (β.app U)) :
    Function.Injective (sectionMap f β U) :=
  (freeOpenAddEquiv (f ⁻¹ᵁ U) N).symm.injective.comp
    (h.comp (freeOpenAddEquiv U M).injective)

theorem sectionMap_restrict {U V : X.Opens} (h : U ≤ V)
    (b : schemeFreeOpen_p0 X V ⟶ M) :
    sectionMap f β U (restrictHom X.ringCatSheaf h b) =
      restrictHom Y.ringCatSheaf (f.preimage_mono h) (sectionMap f β V b) := by
  apply (freeOpenAddEquiv (f ⁻¹ᵁ U) N).injective
  erw [sectionMap_value]
  change β.app U (freeOpenEquiv X.ringCatSheaf M U
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b)) =
    freeOpenEquiv Y.ringCatSheaf N (f ⁻¹ᵁ U)
      (freeOpenMap Y.ringCatSheaf (homOfLE (f.preimage_mono h)) ≫ sectionMap f β V b)
  have hleft := freeOpenEquiv_naturality X.ringCatSheaf M (homOfLE h) b
  have hright := freeOpenEquiv_naturality Y.ringCatSheaf N
    (homOfLE (f.preimage_mono h)) (sectionMap f β V b)
  have hn := PresheafOfModules.naturality_apply β.val (homOfLE h).op
    (freeOpenEquiv X.ringCatSheaf M V b)
  change β.app U (M.presheaf.map (homOfLE h).op _) =
    N.presheaf.map (homOfLE (f.preimage_mono h)).op
      (β.app V (freeOpenAddEquiv V M b)) at hn
  exact (congrArg (β.app U) hleft).trans
    (hn.trans ((congrArg (N.presheaf.map (homOfLE (f.preimage_mono h)).op)
      (sectionMap_value f β V b).symm).trans hright.symm))

def restrictEquiv (N : Y.Modules) {U V : Y.Opens} (h : U ≤ V) (h' : V ≤ U) :
    (schemeFreeOpen_p0 Y V ⟶ N) ≃+ (schemeFreeOpen_p0 Y U ⟶ N) where
  toFun := restrictHom Y.ringCatSheaf h
  invFun := restrictHom Y.ringCatSheaf h'
  left_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  right_inv b := by erw [restrictHom_restrictHom, restrictHom_refl]
  map_add' := restrictHom_add Y.ringCatSheaf h

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PushforwardSectionComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.PushforwardOpenSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher CechH1Transfer

abbrev schemeFreeOpen_p1 (X : Scheme.{0}) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (β : M ⟶ (Scheme.Modules.pushforward f).obj N)
    {J : Type} (U : J → X.Opens)

theorem intersection_preimage {k : ℕ} (t : Fin k → J) :
    intersection (fun i => f ⁻¹ᵁ U i) t = f ⁻¹ᵁ intersection U t := by
  ext x
  simp [intersection, Opens.coe_iInf]

def tupleSectionMap {k : ℕ} (t : Fin k → J) :
    (schemeFreeOpen_p1 X (intersection U t) ⟶ M) →+
      (schemeFreeOpen_p1 Y (intersection (fun i => f ⁻¹ᵁ U i) t) ⟶ N) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).toAddMonoidHom.comp
      (sectionMap f β (intersection U t))

theorem tupleSectionMap_bijective {k : ℕ} (t : Fin k → J)
    (h : Function.Bijective (β.app (intersection U t))) :
    Function.Bijective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).bijective.comp
      (sectionMap_bijective f β _ h)

theorem tupleSectionMap_injective {k : ℕ} (t : Fin k → J)
    (h : Function.Injective (β.app (intersection U t))) :
    Function.Injective (tupleSectionMap f β U t) :=
  (restrictEquiv N (le_of_eq (intersection_preimage f U t))
    (le_of_eq (intersection_preimage f U t).symm)).injective.comp
      (sectionMap_injective f β _ h)

theorem tupleSectionMap_face {k : ℕ} (t : Fin (k+2) → J) (j : Fin (k+2))
    (b : schemeFreeOpen_p1 X (intersection U (t ∘ j.succAbove)) ⟶ M) :
    tupleSectionMap f β U t (restrictHom X.ringCatSheaf (faceLE U t j) b) =
      restrictHom Y.ringCatSheaf (faceLE (fun i => f ⁻¹ᵁ U i) t j)
        (tupleSectionMap f β U (t ∘ j.succAbove) b) := by
  change restrictHom Y.ringCatSheaf _
      (sectionMap f β _ (restrictHom X.ringCatSheaf _ b)) =
    restrictHom Y.ringCatSheaf _
      (restrictHom Y.ringCatSheaf _ (sectionMap f β _ b))
  erw [sectionMap_restrict, restrictHom_restrictHom, restrictHom_restrictHom]

def comparison
    (hvertex : ∀ t : Fin 1 → J, Function.Bijective (β.app (intersection U t)))
    (hpair : ∀ t : Fin 2 → J, Function.Injective (β.app (intersection U t))) :
    SectionComparison U (fun i => f ⁻¹ᵁ U i) M N where
  vertex t := AddEquiv.ofBijective (tupleSectionMap f β U t)
    (tupleSectionMap_bijective f β U t (hvertex t))
  pair t := tupleSectionMap f β U t
  triple t := tupleSectionMap f β U t
  pair_injective t := tupleSectionMap_injective f β U t (hpair t)
  pair_restrict t j b := tupleSectionMap_face f β U t j b
  triple_restrict t j b := tupleSectionMap_face f β U t j b

end
end PiExponent.GeometrySupport.PushforwardOpenSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CurveNormalizationCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponent.CurveZeroPole
open PiExponentSeshadri.Geometry

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

def parameterCurveUnit : (parameterCurve f hf).Modules :=
  SheafOfModules.unit (parameterCurve f hf).ringCatSheaf

instance parameterCurve_isSeparated : (parameterCurve f hf).IsSeparated := by
  rw [Scheme.isSeparated_iff]
  rw [← terminal.comp_from (parameterCurveStructureMap f hf)]
  infer_instance

def parameterCurveAffineOpens (i : Fin 2) : (parameterCurve f hf).Opens :=
  if i = 0 then (zeroChartInclusion f hf).opensRange
  else (infinityChartInclusion f hf).opensRange

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_affine (i : Fin 2) :
    IsAffineOpen (parameterCurveAffineOpens f hf i) := by
  unfold parameterCurveAffineOpens
  split <;> exact isAffineOpen_opensRange _

omit [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E] in
theorem parameterCurveAffineOpens_cover :
    (⨆ i, parameterCurveAffineOpens f hf i) = ⊤ := by
  apply top_le_iff.mp
  intro x _
  rcases parameterCurve_twoChartCover f hf x with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨0, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩
  · apply TopologicalSpace.Opens.mem_iSup.mpr
    exact ⟨1, by simp [parameterCurveAffineOpens, Scheme.Hom.mem_opensRange]⟩

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteSupportCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

variable {X Y : Scheme.{0}}

def pushforwardUnitSections (f : X ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of ℂ)) :
    let _ : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
      Module.compHom _ (Geometry.baseScalars g)
    let _ : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
    Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) ≃ₗ[ℂ] Γ(X,⊤) := by
  dsimp only
  letI : Module ℂ Γ((Scheme.Modules.pushforward f).obj (Geometry.structureSheaf X),⊤) :=
    Module.compHom _ (Geometry.baseScalars g)
  letI : Algebra ℂ Γ(X,⊤) := (Geometry.baseScalars (f ≫ g)).toAlgebra
  refine { Equiv.refl _ with map_add' := fun _ _ => rfl, map_smul' := ?_ }
  intro r a
  change Γ(X,⊤) at a
  change (f.appTop) (Geometry.baseScalars g r) * a = Geometry.baseScalars (f ≫ g) r * a
  congr 1

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry PiExponentSeshadri.Geometry

end PiExponentSeshadri.FiniteSupport

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FiniteLineEuler
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

def overFrame {M : X.Modules} {U : X.Opens}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app M ≪≫ e ≪≫
      (Opens.sheafOfModulesEquivOverUnit U X.ringCatSheaf).symm)
end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.FiniteSupport

section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [DiscreteTopology X]

def pointFrame (L : LineBundle X) (x : X) :
    L.sheaf.val.obj (op (pointOpen x)) ≅
      (structureSheaf X).val.obj (op (pointOpen x)) := by
  let U := (L.locallyRankOne x).choose
  have hx := (L.locallyRankOne x).choose_spec.1
  let e := (L.locallyRankOne x).choose_spec.2.some
  let h : pointOpen x ≤ U := fun y hy => by cases hy; exact hx
  let e' := overFrame e
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over U) (op (Over.mk (homOfLE h)))).mapIso e'

theorem lineBundle_trivial (L : LineBundle X) : Nonempty (L.sheaf ≅ structureSheaf X) := by
  classical
  let F : TopCat.Sheaf AddCommGrpCat.{0} X.toTopCat :=
    (SheafOfModules.toSheaf.{0} X.ringCatSheaf).obj L.sheaf
  let B := pointOpen (X := X)
  let t : ∀ x, Γ(L.sheaf,B x) := fun x => (pointFrame L x).inv (1 : Γ(X,B x))
  have hc : TopCat.Presheaf.IsCompatible F.obj B t := by
    intro x y
    by_cases h : x = y
    · subst y; rfl
    · have he : B x ⊓ B y = ⊥ := by
        ext z
        change (z = x ∧ z = y) ↔ False
        constructor
        · rintro ⟨rfl,h'⟩; exact h h'
        · tauto
      let : Subsingleton (F.obj.obj (op (B x ⊓ B y))) :=
        AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty he).isZero
      exact Subsingleton.elim _ _
  have hcover : (⊤ : X.Opens) ≤ ⨆ x, B x := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x,rfl⟩
  obtain ⟨a,ha,_⟩ := F.existsUnique_gluing' B ⊤ (fun _ => homOfLE le_top) hcover t hc
  let s : structureSheaf X ⟶ L.sheaf :=
    (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).symm a
  have hs (x : X) : s.val.app (op (B x)) = (pointFrame L x).inv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change Γ(X,B x) at r
    have hs1 : s.val.app (op (B x)) (1 : Γ(X,B x)) = t x := by
      have htop : s.app ⊤ (1 : Γ(X,⊤)) = a :=
        (FlasqueCohomology.globalHomEquiv X.ringCatSheaf L.sheaf).apply_symm_apply a
      have hn := CategoryTheory.congr_fun (s.mapPresheaf.naturality
        (homOfLE (show B x ≤ ⊤ from le_top)).op) (1 : Γ(X,⊤))
      change s.app (B x) (X.presheaf.map (homOfLE le_top).op 1) =
        L.sheaf.presheaf.map (homOfLE le_top).op (s.app ⊤ (1 : Γ(X,⊤))) at hn
      have hax : L.sheaf.presheaf.map (homOfLE (show B x ≤ ⊤ from le_top)).op a = t x := ha x
      have hn' : s.app (B x) (1 : Γ(X,B x)) =
          L.sheaf.presheaf.map (homOfLE le_top).op a := by
        simpa only [map_one, htop] using hn
      exact hn'.trans hax
    let : Module Γ(X,B x) (L.sheaf.val.obj (op (B x))) :=
      (L.sheaf.val.obj (op (B x))).isModule
    calc
      s.val.app (op (B x)) r = r • s.val.app (op (B x)) (1 : Γ(X,B x)) := by
        exact (congrArg (s.val.app (op (B x))) (mul_one r).symm).trans
          ((s.val.app (op (B x))).hom.map_smul r (1 : Γ(X,B x)))
      _ = r • (pointFrame L x).inv (1 : Γ(X,B x)) := by rw [hs1]
      _ = (pointFrame L x).inv r := by
        exact ((pointFrame L x).inv.hom.map_smul r (1 : Γ(X,B x))).symm.trans
          (congrArg (pointFrame L x).inv (mul_one r))
  have hiso : IsIso ((SheafOfModules.toSheaf.{0} X.ringCatSheaf).map s) := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis pointOpen_basis
    intro x
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map (s.val.app (op (B x))))
    rw [hs]
    infer_instance
  let : Mono s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).mono_of_mono_map inferInstance
  let : Epi s := (SheafOfModules.toSheaf.{0} X.ringCatSheaf).epi_of_epi_map inferInstance
  let : IsIso s := isIso_of_mono_of_epi s
  exact ⟨(asIso s).symm⟩

end

open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry

end PiExponentSeshadri.FiniteSupport

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CartierSequence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.CartierSequence
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem exact (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :
    ∃ hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0,
      (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).ShortExact := by
  have local_exact (U : X.affineOpens)
      (e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
      (hI : I.ideal U = Ideal.span {U.1.topIso.hom
        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}) :=
    PrincipalSequence.exact (I.subschemeι ∣_ U.1)
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
      (restriction_principal p I U _ hI)
  have hz : φ ≫ LineClosedUnit.map I.subschemeι N = 0 := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U,hx,e,d,hI⟩ := heq x
    obtain ⟨hzero,hex⟩ := local_exact U e d hI
    refine ⟨U.1,hx,?_⟩
    apply (cancel_epi e.inv).mp
    apply (cancel_mono (LineClosedUnit.frame I.subschemeι N U.1 d).hom).mp
    rw [Functor.map_comp,comp_zero,zero_comp]
    rw [Category.assoc,Category.assoc]
    rw [← d.hom_inv_id_assoc ((Scheme.Modules.restrictFunctor U.1.ι).map
      (LineClosedUnit.map I.subschemeι N))]
    simp only [Category.assoc]
    rw [LineClosedUnit.framed_map]
    simpa only [Category.assoc] using! hzero
  refine ⟨hz,{ exact := ?_, epi_g := LineClosedUnit.epi _ _ }⟩
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U,hx,e,d,hI⟩ := heq x
  obtain ⟨hzero,hex⟩ := local_exact U e d hI
  refine ⟨U.1,hx,?_⟩
  let S := (ShortComplex.mk φ (LineClosedUnit.map I.subschemeι N) hz).map
    (Scheme.Modules.restrictFunctor U.1.ι)
  let T := ShortComplex.mk (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)
    (IdealModule.structureMap (I.subschemeι ∣_ U.1)) hzero
  let ee : S ≅ T := ShortComplex.isoMk e d (LineClosedUnit.frame I.subschemeι N U.1 d)
    (by simp [S,T] <;> exact Iso.hom_inv_id_assoc _ _) (by
      change d.hom ≫ IdealModule.structureMap (I.subschemeι ∣_ U.1) =
        (Scheme.Modules.restrictFunctor U.1.ι).map (LineClosedUnit.map I.subschemeι N) ≫ _
      rw [← LineClosedUnit.framed_map I.subschemeι N U.1 d]
      exact d.hom_inv_id_assoc _)
  exact ShortComplex.exact_of_iso ee.symm hex.exact

end
end PiExponentSeshadri.CartierSequence

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveEffectiveTwist
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.CurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}} [IsIntegral X]

theorem lineBundle_not_isZero (L : LineBundle X) : ¬ IsZero L.sheaf := by
  intro h
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty U := ⟨⟨x, hx⟩⟩
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hL : (𝟙 L.sheaf) = 0 := h.eq_of_src _ _
  have hr := congrArg (Scheme.Modules.restrictFunctor U.ι).map hL
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at hr
  have hid : (𝟙 (O U.toScheme)) = 0 := by
    simpa only [O] using! id_eq_zero_of_iso e hr
  have hh := congrArg (endValue (X := U.toScheme)) hid
  simp only [endValue] at hh
  exact one_ne_zero (show (1 : Γ(U.toScheme, ⊤)) = 0 from hh)

omit [IsIntegral X] in

theorem section_ne_zero_of_mem_isoOpen (L : LineBundle X) (s : O X ⟶ L.sheaf)
    (x : X) (hx : x ∈ isoOpen s) : s ≠ 0 := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have hm : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ isoOpen s := hx
  rw [preimage_isoOpen s U.ι e] at hm
  intro hz
  subst s
  have hrestrict : restrictSection U.ι (0 : O X ⟶ L.sheaf) = 0 := by
    simpa only [restrictSection] using restrictSection_zero (M := L.sheaf) U.ι
  have hz := (congrArg (coefficient e) hrestrict).trans (coefficient_zero e)
  erw [hz, Scheme.basicOpen_zero] at hm
  exact hm

theorem nonzero_section_of_generators (L : LineBundle X) (G : L.sheaf.GeneratingSections) :
    ∃ s : GlobalSections X L.sheaf, s ≠ 0 := by
  classical
  by_contra h
  push Not at h
  exact lineBundle_not_isZero L (generators_isZero X.ringCatSheaf L.sheaf G h)

end
end PiExponent.CurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelFieldEmbedding
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurveProjection_isFinite _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurveStructureMap_isProper _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_isSeparated _root_.OAI.PiExponent.CurveNormalizationModel.parameterCurve_noetherian _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open CategoryTheory AlgebraicGeometry
open scoped Polynomial nonZeroDivisors
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [FiniteDimensional (IntermediateField.adjoin F {f}) E]

theorem parameterCurveFunctionFieldEquiv_eq_infinity :
    letI : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
      (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
    letI := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
    (parameterCurveFunctionFieldEquiv f hf).toRingHom =
      affineChartFunctionFieldMap (parameterChart f⁻¹ (transcendental_inverse f hf)) E
        (infinityChartInclusion f hf) := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  let := parameterChartFractionRing f hf
  let := parameterChartFractionRing f⁻¹ (transcendental_inverse f hf)
  let := parameterLaurentChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  let : Algebra (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) :=
    ((reciprocalLaurentChartEquiv f hf).symm.toRingHom.comp
      (parameterChartOverlapHom f⁻¹ (transcendental_inverse f hf))).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (parameterChart f⁻¹ (transcendental_inverse f hf))
      (parameterLaurentChart f hf) E := IsScalarTower.of_algebraMap_eq' rfl
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f hf) (parameterLaurentChart f hf)))) :=
    zeroOverlap_isOpenImmersion f hf
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (parameterChart f⁻¹ (transcendental_inverse f hf))
        (parameterLaurentChart f hf)))) := infinityOverlap_isOpenImmersion f hf
  change affineChartFunctionFieldMap (parameterChart f hf) E (zeroChartInclusion f hf) = _
  exact affineChartFunctionFieldMap_eq_of_overlap (parameterChart f hf) E
    (parameterChart f⁻¹ (transcendental_inverse f hf)) (parameterLaurentChart f hf)
    (zeroChartInclusion f hf) (infinityChartInclusion f hf)
    (parameterCurve_overlap_compatibility f hf)

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetSupport
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetSupport
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity
variable {X Y : Scheme}

def localQuotientEquiv (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Γ((moduleTwistFunctor A n).obj (jetQuotient I), U.1) ≃
      (Γ(X,U.1) ⧸ I.ideal U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj (jetQuotient I)) U.1).symm.addCommGroupIsoToAddEquiv.toEquiv |>.trans
    ((sectionsIso ((moduleTwistRestrictFrame A U.1 e n).app (jetQuotient I)) ⊤).addCommGroupIsoToAddEquiv.toEquiv.trans
      ((restrictionSectionsIso (jetQuotient I) U.1).addCommGroupIsoToAddEquiv.toEquiv.trans
        (I.subschemeObjIso U).commRingCatIsoToRingEquiv.toEquiv))

def globalQuotientValue (I : X.IdealSheafData) (A : LineBundle X) (n : ℕ)
    (U : X.affineOpens) (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X ((moduleTwistFunctor A n).obj (jetQuotient I))) :
    Γ(X,U.1) ⧸ I.ideal U :=
  localQuotientEquiv I A n U e
    (((moduleTwistFunctor A n).obj (jetQuotient I)).presheaf.map
      (homOfLE (le_top : U.1 ≤ ⊤)).op
      (moduleSectionEquiv ((moduleTwistFunctor A n).obj (jetQuotient I)) s))

end PiExponent.AffineJetSupport
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AffineJetQuotient
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AffineJetQuotient
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.BlowupJetSurjectivity PiExponent.AffineJetSupport
variable {X : Scheme}

def untwistSectionsIso (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) (M : X.Modules) :
    Γ((moduleTwistFunctor A n).obj M,U) ≅ Γ(M,U) :=
  (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).symm ≪≫
    sectionsIso ((moduleTwistRestrictFrame A U e n).app M) ⊤ ≪≫
    restrictionSectionsIso M U

@[reassoc] theorem untwistSectionsIso_natural (A : LineBundle X) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ)
    {M N : X.Modules} (f : M ⟶ N) :
    ((moduleTwistFunctor A n).map f).app U ≫ (untwistSectionsIso A U e n N).hom =
      (untwistSectionsIso A U e n M).hom ≫ f.app U := by
  have hn := congrArg (fun g => g.app ⊤)
    ((moduleTwistRestrictFrame A U e n).hom.naturality f)
  simp only [Scheme.Modules.Hom.comp_app] at hn
  change ((Scheme.Modules.restrictFunctor U.ι).map ((moduleTwistFunctor A n).map f)).app ⊤ ≫
      ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ =
    ((moduleTwistRestrictFrame A U e n).app M).hom.app ⊤ ≫
      ((Scheme.Modules.restrictFunctor U.ι).map f).app ⊤ at hn
  apply (cancel_epi (restrictionSectionsIso ((moduleTwistFunctor A n).obj M) U).hom).mp
  simp only [untwistSectionsIso, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← restrictionSectionsIso_natural_assoc]
  simp only [Iso.hom_inv_id_assoc]
  change _ ≫ ((moduleTwistRestrictFrame A U e n).app N).hom.app ⊤ ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc, restrictionSectionsIso_natural]
  rfl

def globalSectionCoefficient (A : LineBundle X) (n : ℕ) (U : X.affineOpens)
    (e : A.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme)
    (s : GlobalSections X (modulePow X A.sheaf n)) : Γ(X,U.1) :=
  (untwistSectionsIso A U.1 e n (structureSheaf X)).hom
    ((s ≫ (moduleTwistUnitIso A n).inv).app U.1 (1 : Γ(X,U.1)))

end PiExponent.AffineJetQuotient
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_JetCenterIdentification
attribute [-instance] _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_isOpenImmersion _root_.OAI.PiExponent.AdmissibleBlowupGeometry.affineChart_quasiCompact _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
namespace PiExponent.JetCenterIdentification
open CurveValuationCenter PlaceValuationRing CompactLogJetIdeal CompactJetPolynomial

variable {E : Type} [Field E] [Algebra ℂ E]

theorem centered_of_closedPoint_eq {m : ℕ} (p : NormalizedPlace ℂ E)
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j]
    (q : Spec (CommRingCat.of (ring p)) ⟶ X)
    (hgeneric : Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ q =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hclosed : q (IsLocalRing.closedPoint (ring p)) = j (centerPoint c)) :
    CurveCenters.Centered z (Fin.cases 1 c) p := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map q.continuous).mem_open
      j.isOpenEmbedding.isOpen_range (hclosed ▸ Set.mem_range_self (centerPoint c))
  let g := IsOpenImmersion.lift j q hr
  have hg : g ≫ j = q := IsOpenImmersion.lift_fac j q hr
  let φ : coordinateRing m →+* ring p := (Spec.preimage g).hom
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
  have hcomp : CommRingCat.ofHom φ ≫ CommRingCat.ofHom (algebraMap (ring p) E) =
      CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp, hgφ]
    apply (cancel_mono j).mp
    rw [Category.assoc, hg]
    exact hgeneric
  have hgc : g (IsLocalRing.closedPoint (ring p)) = centerPoint c := by
    apply j.isOpenEmbedding.injective
    change (g ≫ j) (IsLocalRing.closedPoint (ring p)) = _
    rw [hg, hclosed]
  have hcomap : PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p)) =
      centerPoint c := by
    change (Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint (ring p)) = _
    rw [hgφ, hgc]
  intro i
  let P : coordinateRing m := MvPolynomial.X i - MvPolynomial.C (center c i)
  have hmem : φ P ∈ IsLocalRing.maximalIdeal (ring p) := by
    change P ∈ (PrimeSpectrum.comap φ (IsLocalRing.closedPoint (ring p))).asIdeal
    rw [hcomap]
    change P ∈ WeightedBezout.pointIdeal (center c)
    rw [WeightedBezout.mem_pointIdeal]
    simp [P]
  have hpos := p.valuation.toValuation.mem_maximalIdeal_iff.mp hmem
  have heval := congrArg
    (fun f : CommRingCat.of (coordinateRing m) ⟶ CommRingCat.of E => f P) hcomp
  change algebraMap (ring p) E (φ P) = MvPolynomial.aeval z P at heval
  change 0 < p.valuation (algebraMap (ring p) E (φ P)) at hpos
  rw [heval] at hpos
  simpa [P, center] using hpos

end PiExponent.JetCenterIdentification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.WeightedMonomialPole

open WeightedCurveDegree WeightedPolynomialPole PolynomialPoleBound

variable {K ι : Type*} [Field K] [Fintype ι]

theorem monomial_order_lower (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) (a : ι → ℕ) {R : ℚ}
    (ha : (∑ i, w i * (a i : ℚ)) ≤ R) :
    ((-(R : ℝ) * (coordinatePole v x w : ℝ) : ℝ) : WithTop ℝ) ≤
      realValuation v (∏ i, x i ^ a i) := by
  have hq : -R * coordinatePole v x w ≤
      ∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ) := by
    have h := monomial_pole_le w (fun i => (coordinateOrder v (x i) : ℚ)) hw a ha
    change -(∑ i, (a i : ℚ) * (coordinateOrder v (x i) : ℚ)) ≤ R * coordinatePole v x w at h
    linarith
  have hr : -(R : ℝ) * (coordinatePole v x w : ℝ) ≤
      ∑ i, (a i : ℝ) * (coordinateOrder v (x i) : ℝ) := by exact_mod_cast hq
  apply (WithTop.coe_le_coe.mpr hr).trans
  rw [WithTop.coe_sum, valuation_prod]
  apply Finset.sum_le_sum
  intro i hi
  rw [(realValuation v).map_pow]
  simpa only [← WithTop.coe_nsmul, nsmul_eq_mul] using
    nsmul_le_nsmul_right (coordinateOrder_le_realValuation v (x i)) (a i)

theorem exists_attaining_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (_hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w := by
  by_cases hD : coordinatePole v x w = 0
  · refine ⟨0, hzero, by simp, ?_⟩
    simp [hD, coordinateOrder, integerOrder_one]
  have hDpos : 0 < coordinatePole v x w :=
    lt_of_le_of_ne (weightedPole_nonneg w _) (Ne.symm hD)
  obtain ⟨o, _, ho⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option ι))) Finset.univ_nonempty
    (fun i => i.elim 0 (fun j => -(coordinateOrder v (x j) : ℚ) / w j))
  change coordinatePole v x w = _ at ho
  cases o with
  | none => exact False.elim (hD ho)
  | some i =>
    change coordinatePole v x w = -(coordinateOrder v (x i) : ℚ) / w i at ho
    have hx : x i ≠ 0 := by
      intro hx
      have hh : coordinatePole v x w = 0 := by simpa [hx, coordinateOrder] using ho
      exact hD hh
    have heval : (∏ j, x j ^ (Pi.single i (powers i) : ι → ℕ) j) = x i ^ powers i := by
      simp [Pi.single_apply]
    refine ⟨Pi.single i (powers i), hpure i, ?_, ?_⟩
    · rw [heval]
      exact pow_ne_zero _ hx
    · rw [heval, coordinateOrder_pow v (x i) hx]
      push_cast
      change (powers i : ℚ) * (coordinateOrder v (x i) : ℚ) = -R * coordinatePole v x w
      rw [ho, ← hpowers i]
      field_simp [ne_of_gt (hw i)]

theorem exists_minimizing_monomial [DecidableEq ι]
    (v : AddValuation K (WithTop ℤ)) (x : ι → K)
    (w : ι → ℚ) (hw : ∀ i, 0 < w i) {R : ℚ} (hR : 0 < R)
    (powers : ι → ℕ) (hpowers : ∀ i, w i * (powers i : ℚ) = R)
    (M : Finset (ι → ℕ)) (hzero : 0 ∈ M)
    (hpure : ∀ i, Pi.single i (powers i) ∈ M)
    (hbudget : ∀ a ∈ M, (∑ i, w i * (a i : ℚ)) ≤ R) :
    ∃ a ∈ M, (∏ i, x i ^ a i) ≠ 0 ∧
      (coordinateOrder v (∏ i, x i ^ a i) : ℚ) = -R * coordinatePole v x w ∧
      ∀ b ∈ M, v (∏ i, x i ^ a i) ≤ v (∏ i, x i ^ b i) := by
  obtain ⟨a,ha,han,hao⟩ := exists_attaining_monomial v x w hw hR powers hpowers M hzero hpure
  refine ⟨a,ha,han,hao,?_⟩
  intro b hb
  apply (realValuation_le_iff v _ _).mp
  rw [realValuation_of_ne_zero v _ han]
  have he : (coordinateOrder v (∏ i, x i ^ a i) : ℝ) =
      -(R : ℝ) * (coordinatePole v x w : ℝ) := by exact_mod_cast hao
  rw [he]
  exact monomial_order_lower v x w hw b (hbudget b hb)

end PiExponent.WeightedMonomialPole

end

end OAI
end


