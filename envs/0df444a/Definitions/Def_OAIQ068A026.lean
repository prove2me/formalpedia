-- Prove2me | Definitions.Def_OAIQ068A026
-- name    : OAIQ068A026
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:00:45.156951+00:00
-- url     : https://prove2.me/theorems/a0e880b7-f907-4a77-9ecb-9e90c11a9a11
-- title:
--   Definitions bundle OAIQ068A026 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 89 declarations of OpenAI's Lean: 42 definitions, 2 instances and 45 theorems. The definitions and types are `OAI.PiExponent.NumericalAmpleness.cartierPowerMultiply`, `OAI.PiExponent.NumericalAmpleness.localCoefficientAddHom`, `OAI.PiExponent.NumericalAmpleness.sectionLinearCombination`, `OAI.PiExponent.RamifiedLocalLength.translatedPowerLocalBasis`, `OAI.PiExponent.ReducedComponentAmple.closedBaseChangeLineIso`, `OAI.PiExponent.ReesFrozenChart.base`, `OAI.PiExponent.ReesFrozenChart.coordinateEquiv`, `OAI.PiExponent.ReesFrozenChart.coordinateInv`, `OAI.PiExponent.ReesFrozenChart.coordinateRing`, `OAI.PiExponent.ReesFrozenChart.restriction`, `OAI.PiExponent.ReesFrozenPower.pieceEquiv`, `OAI.PiExponent.ReesFrozenPower.powerEquiv`, `OAI.PiExponent.ReesLocalizedIntersections.LocalizationModule`, `OAI.PiExponent.ReesLocalizedIntersections.Piece`, `OAI.PiExponent.ReesLocalizedIntersections.localizationEvaluation`, `OAI.PiExponent.ReesLocalizedIntersections.pieceEvaluation`, `OAI.PiExponent.ReesProductAugmentation.ordinaryFraction`, `OAI.PiExponent.ReesProductChart.Chart`, `OAI.PiExponent.ReesProductChart.chartBase`, `OAI.PiExponent.ReesProductChart.chartMap`, `OAI.PiExponent.ReesProductChart.productGenerator`, `OAI.PiExponent.ReesProductChart.ratio`, `OAI.PiExponent.ReesProductPower.chartPowerEquiv`, `OAI.PiExponent.ReesProductPower.chartPowerMap`, `OAI.PiExponent.ReesProductPowerSections.chartEquation`, `OAI.PiExponent.ReesProductRestriction.chartPowerRestriction`, `OAI.PiExponent.ReesProductRestriction.chartRestriction`, `OAI.PiExponent.TranslatedPowerCover.basis`, `OAI.PiExponent.TranslatedPowerCover.decomposition`, `OAI.PiExponent.TupleCechBound.FullSupport`, `OAI.PiExponent.TupleCechBound.extend`, `OAI.PiExponent.TupleCechBound.pullback`, `OAI.PiExponent.WeightedChartRingEvaluation.ambientOpen`, `OAI.PiExponent.formalJetEvaluation`, `OAI.PiExponent.literalJetSubstitution`, `OAI.PiExponentApprox.TransverseMultiplicity.RectangularRing`, `OAI.PiExponentApprox.TransverseMultiplicity.rectIndexEquiv`, `OAI.PiExponentApprox.TransverseMultiplicity.rectangularAugmentationIdeal`, `OAI.PiExponentApprox.TransverseMultiplicity.rectangularCotangentFirstCoefficients`, `OAI.PiExponentApprox.TransverseMultiplicity.rectangularFirstCoefficients` and 2 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ClosedAmpleBaseChange`, `PiExponent_Ampleness_NakaiCartier`, `PiExponent_Ampleness_ReesFixedChart`, `PiExponent_Ampleness_ReesFixedPower`, `PiExponent_Ampleness_ReesFixedPowerRestriction`, `PiExponent_Ampleness_ReesFixedRestriction`, `PiExponent_Ampleness_ReesLocalizedIntersections`, `PiExponent_Ampleness_ReesProductAugmentation`, `PiExponent_Ampleness_ReesProductChart`, `PiExponent_Ampleness_ReesProductPower`, `PiExponent_Ampleness_ReesProductRestriction`, `PiExponent_Ampleness_ReesProductSchemeChart`, `PiExponent_Approximation_RegularSectionChoice`, `PiExponent_Cohomology_ReesSheafCechBase`, `PiExponent_Cohomology_TupleCechBound`, `PiExponent_Geometry_PlaceCenteredBranch`, `PiExponent_Jets_AuxiliaryJetMap`, `PiExponent_Jets_FormalAuxiliaryJet`, `PiExponent_Jets_RectangularCotangent`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_IdealModule`, `PiExponent_LocalAlgebra_RamifiedPowerLength`, `PiExponent_LocalAlgebra_WeightedChartRingEvaluation`, `PiExponent_Polynomials_TranslatedPowerCover`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015`, `OAIQ068A016`, `OAIQ068A017` and `OAIQ068A018` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A033`; the proofs of `OAI_PiExponent_CurveInequality_excess_implies_zeroth_eq_one`, `OAI.PiExponent.CurveInequality.excess_implies_zeroth_eq_one_q68`, `OAI_PiExponent_PrimeWeightedBezout_weighted_prime_length_bound` and `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A014
import Definitions.Def_OAIQ068A015
import Definitions.Def_OAIQ068A016
import Definitions.Def_OAIQ068A017
import Definitions.Def_OAIQ068A018

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ClosedAmpleBaseChange
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ReducedComponentAmple
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

def closedBaseChangeLineIso (I : X.IdealSheafData) (f : Y ⟶ X) (L : LineBundle X) :
    ((L.pullback I.subschemeι).pullback (closedBaseChange I f)).sheaf ≅
      ((L.pullback f).pullback (I.comap f).subschemeι).sheaf :=
  (Scheme.Modules.pullbackComp (closedBaseChange I f) I.subschemeι).app L.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (closedBaseChange_condition I f)).app L.sheaf ≪≫
    ((Scheme.Modules.pullbackComp (I.comap f).subschemeι f).app L.sheaf).symm

end PiExponent.ReducedComponentAmple

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_NakaiCartier
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cartierPowerMultiply (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    modulePow X L.sheaf n ⟶ modulePow X L.sheaf (n+1) :=
  (moduleTensorUnit (modulePow X L.sheaf n)).inv ≫
    moduleTensorMap s (𝟙 (modulePow X L.sheaf n))

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealModule
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end PiExponentSeshadri.IdealModule

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesLocalizedIntersections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesLocalizedIntersections
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] [DecidableEq J] in
theorem evaluation_presentation_product (s : Finset J) :
    evaluation I (presentation I a (coverProduct MvPolynomial.X s)) = coefficientProduct I a s := by
  simp only [coverProduct, coefficientProduct, map_prod, presentation_X, evaluation_generator]

abbrev LocalizationModule (s : Finset J) :=
  letI := presentationAlgebra I a
  LocalizedModule (Submonoid.powers (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s))
    (reesAlgebra I)

def localizationEvaluation (s : Finset J) :
    LocalizationModule I a s →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation (Submonoid.powers (coverProduct MvPolynomial.X s))
    (Submonoid.powers (coefficientProduct I a s)) (evaluation I) (by
      rintro ⟨_, k, rfl⟩
      refine ⟨k, ?_⟩
      change coefficientProduct I a s ^ k =
        evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k))
      rw [map_pow, map_pow, evaluation_presentation_product])

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_fraction (s : Finset J) (m : reesAlgebra I) (k : ℕ) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (fraction
      (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  let := presentationAlgebra I a
  unfold localizationEvaluation fraction
  rw [LocalizedAlgebraEvaluation.evaluation_mk]
  congr 1
  apply Subtype.ext
  change evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k)) =
    coefficientProduct I a s ^ k
  rw [map_pow, map_pow, evaluation_presentation_product]

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (p • z) =
      algebraMap R (Localization.Away (coefficientProduct I a s))
        (evaluation I (presentation I a p)) * localizationEvaluation I a s z := by
  let := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation_smul _ _ _ _ p z

omit [Fintype J] in
theorem localizationEvaluation_restriction {s t : Finset J} (hst : s ⊆ t)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a t
      (restriction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
        (coverProduct MvPolynomial.X t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z) =
      coefficientRestriction I a hst (localizationEvaluation I a s z) := by
  let := presentationAlgebra I a
  induction z using LocalizedModule.induction_on with
  | h m den =>
    obtain ⟨k, hk⟩ := den.property
    have hd : den = powerDenominator (coverProduct MvPolynomial.X s) k := Subtype.ext hk.symm
    subst den
    change localizationEvaluation I a t (restriction _ _ _ (fraction _ m k)) =
      coefficientRestriction I a hst (localizationEvaluation I a s (fraction _ m k))
    have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
        (coefficientProduct I a s)) :=
      IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
        exact Finset.prod_dvd_prod_of_subset s t _ hst)
    apply (hu.pow k).mul_right_injective
    calc
      _ = localizationEvaluation I a t
          (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s ^ k •
            restriction _ _ _ (fraction _ m k)) := by
        rw [localizationEvaluation_smul, map_pow, map_pow,
          evaluation_presentation_product, map_pow]
      _ = localizationEvaluation I a t (fraction (coverProduct MvPolynomial.X t) m 0) := by
        rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
      _ = algebraMap R (Localization.Away (coefficientProduct I a t)) (evaluation I m) := by
        rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
      _ = _ := by
        have hspec := congrArg (coefficientRestriction I a hst)
          (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s))
            (evaluation I m) (powerDenominator (coefficientProduct I a s) k))
        rw [localizationEvaluation_fraction]
        simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow]
          using hspec.symm

abbrev Piece (s : Finset J) (n : ℕ) :=
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  IntersectionPiece (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem s n

def pieceEvaluation (s : Finset J) (n : ℕ) :
    Piece I a s n →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (localizationEvaluation I a s).comp (Piece I a s n).subtype

theorem pieceEvaluation_restriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    pieceEvaluation I a t n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      coefficientRestriction I a hst (pieceEvaluation I a s n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  exact localizationEvaluation_restriction I a hst z.val

theorem pieceEvaluation_injective (s : Finset J) (n : ℕ) :
    Function.Injective (pieceEvaluation I a s n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hp : presentation I a (coverProduct MvPolynomial.X s) ∈ piece I s.card :=
    presentation_integer_mem I a
      (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)
  have heval : evaluation I m = (m : Polynomial R).coeff (n + k * s.card) :=
    evaluation_piece I ⟨m, hm'⟩
  have hep : evaluation I (presentation I a (coverProduct MvPolynomial.X s)) =
      (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, hp⟩
  change localizationEvaluation I a s z.val = 0 at hz
  rw [hrep, localizationEvaluation_fraction] at hz
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hz
  obtain ⟨l, rfl⟩ := hb
  apply Subtype.ext
  change z.val = 0
  rw [hrep, fraction_eq_zero]
  refine ⟨l, ?_⟩
  change presentation I a (coverProduct MvPolynomial.X s ^ l) * m = 0
  rw [map_pow]
  apply Subtype.ext
  change (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R) ^ l *
    (m : Polynomial R) = 0
  rw [(mem_piece I s.card _).mp hp, (mem_piece I (n + k * s.card) m).mp hm',
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
  rw [← hep, evaluation_presentation_product]
  rw [heval] at hbm
  simp only [hbm, map_zero]

end
end PiExponent.ReesLocalizedIntersections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductChart
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def productGenerator (s : Finset J) : reesAlgebra I :=
  presentation I a (coverProduct MvPolynomial.X s)

theorem productGenerator_mem (s : Finset J) : productGenerator I a s ∈ piece I s.card :=
  presentation_integer_mem I a
    (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)

omit [Fintype J] [DecidableEq J] in
theorem evaluation_productGenerator (s : Finset J) :
    evaluation I (productGenerator I a s) = coefficientProduct I a s :=
  evaluation_presentation_product I a s

omit [Fintype J] [DecidableEq J] in
theorem productGenerator_eq_prod (s : Finset J) :
    productGenerator I a s = ∏ j ∈ s, generator I (a j) := by
  simp only [productGenerator, coverProduct, map_prod, presentation_X]

abbrev Chart (s : Finset J) := HomogeneousLocalization.Away (piece I) (productGenerator I a s)

def chartMap (s : Finset J) : Chart I a s →+* Localization.Away (coefficientProduct I a s) :=
  (IsLocalization.map (M := Submonoid.powers (productGenerator I a s))
    (S := Localization.Away (productGenerator I a s))
    (T := Submonoid.powers (coefficientProduct I a s))
    (Localization.Away (coefficientProduct I a s)) (evaluation I)
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp only [map_pow, evaluation_productGenerator]⟩)).comp
      (algebraMap (Chart I a s) (Localization.Away (productGenerator I a s)))

theorem chartMap_mk (s : Finset J) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • s.card)) :
    chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

theorem chartMap_injective (s : Finset J) : Function.Injective (chartMap I a s) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) z
  have hzero := RingHom.mem_ker.mp hz
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hzero
  obtain ⟨l, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨productGenerator I a s ^ l, ⟨l, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have he : evaluation I m = (m : Polynomial R).coeff (k • s.card) := evaluation_piece I ⟨m, hm⟩
  have hep : evaluation I (productGenerator I a s) =
      (productGenerator I a s : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, productGenerator_mem I a s⟩
  change (productGenerator I a s : Polynomial R) ^ l * (m : Polynomial R) = 0
  rw [(mem_piece I (k • s.card) m).mp hm,
    (mem_piece I s.card _).mp (productGenerator_mem I a s),
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    ← hep, evaluation_productGenerator]
  rw [he] at hbm
  simp only [hbm, map_zero]

def chartBase (s : Finset J) : R →+* Chart I a s :=
  (HomogeneousLocalization.fromZeroRingHom (piece I)
    (Submonoid.powers (productGenerator I a s))).comp (zeroEquiv I).toRingHom

theorem chartMap_base (s : Finset J) (r : R) :
    chartMap I a s (chartBase I a s r) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • s.card) := by
    simp [mem_piece]
  refine (chartMap_mk I a s 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he, powerDenominator_zero, IsLocalization.mk'_one]

variable {s : Finset J} {j : J} (hj : j ∈ s)
include hj

def ratio (b : I) : Chart I a s :=
  HomogeneousLocalization.Away.mk (piece I) (productGenerator_mem I a s) 1
    (generator I b * productGenerator I a (s.erase j)) (by
      have h := SetLike.mul_mem_graded (generator_mem I b)
        (productGenerator_mem I a (s.erase j))
      simpa only [one_nsmul, Nat.add_comm 1, Finset.card_erase_add_one hj] using h)

theorem chartMap_ratio (b : I) :
    chartMap I a s (ratio I a hj b) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s))
        (b.val * coefficientProduct I a (s.erase j))
        (powerDenominator (coefficientProduct I a s) 1) := by
  rw [ratio, chartMap_mk, map_mul, evaluation_generator, evaluation_productGenerator]

theorem base_mul_ratio (b : I) :
    chartBase I a s (a j).val * ratio I a hj b = chartBase I a s b.val := by
  apply chartMap_injective I a s
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  rw [← map_mul]
  congr 1
  change (a j).val * (b.val * coefficientProduct I a (s.erase j)) =
    b.val * coefficientProduct I a s ^ 1
  rw [pow_one, coefficientProduct_eq_pivot I a hj]
  ring

theorem map_ideal_principal :
    I.map (chartBase I a s) = Ideal.span {chartBase I a s (a j).val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a s b ∈ Ideal.span {chartBase I a s (a j).val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a hj ⟨b, hb⟩, (base_mul_ratio I a hj ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ (a j).property

theorem chart_ordinaryPower_principal (n : ℕ) :
    (I ^ n).map (chartBase I a s) = Ideal.span {(chartBase I a s (a j).val) ^ n} := by
  rw [Ideal.map_pow, map_ideal_principal I a hj, Ideal.span_singleton_pow]

theorem chart_generator_regular : IsRegular (chartBase I a s (a j).val) := by
  have hu : IsUnit (chartMap I a s (chartBase I a s (a j).val)) := by
    rw [chartMap_base]
    exact IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a s)
      ⟨coefficientProduct I a (s.erase j), coefficientProduct_eq_pivot I a hj⟩
  constructor
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a s) h
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a s) h

end
end PiExponent.ReesProductChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductSchemeChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

variable {p : J} (hp : p ∈ s)

def chartEquation : Γ(Spec (CommRingCat.of (Chart I a s)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv
    (ReesProductChart.chartBase I a s (a p).val)

include hp in
theorem chartEquation_regular : IsLeftRegular (chartEquation I a (s := s) (p := p)) := by
  exact PiExponentSeshadri.IdealModule.regular_map_flat _
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv))
    (ReesProductChart.chart_generator_regular I a hp).left

end PiExponent.ReesProductPowerSections
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem exists_coordinateRing : ∃ C : CommRingCat, C = CommRingCat.of (Chart I a s) := ⟨_,rfl⟩
def coordinateRing : CommRingCat := (exists_coordinateRing I a s).choose
omit [Fintype J] [DecidableEq J] in
theorem coordinateRing_eq : coordinateRing I a s = CommRingCat.of (Chart I a s) :=
  (exists_coordinateRing I a s).choose_spec

def coordinateEquiv : coordinateRing I a s ≃+* Chart I a s :=
  (eqToIso (coordinateRing_eq I a s)).commRingCatIsoToRingEquiv

abbrev coordinateInv : CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s :=
  CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom

def base : R →+* coordinateRing I a s :=
  (coordinateInv I a s).hom.comp (ReesProductChart.chartBase I a s)

instance coordinateInv_isIso :
    IsIso (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
    CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) := by
  change IsIso (eqToIso (coordinateRing_eq I a s)).inv
  infer_instance

local instance coordinateSpec_isIso :
    IsIso (Spec.map (coordinateInv I a s)) :=
  inferInstanceAs (IsIso
    (Scheme.Spec.mapIso (eqToIso (coordinateRing_eq I a s)).symm.op).hom)

end
end PiExponent.ReesFrozenChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductPower
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductPower
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} {j : J} (hj : j ∈ s)
include hj

theorem pieceEvaluation_mem_chartPower (n : ℕ) (z : Piece I a s n) :
    ∃ q : ↥((I ^ n).map (ReesProductChart.chartBase I a s)),
      ReesProductChart.chartMap I a s q.val = pieceEvaluation I a s n z := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hc : s.card = (s.erase j).card + 1 := (Finset.card_erase_add_one hj).symm
  have hdeg : (n + k * s.card) + n • (s.erase j).card = (n + k) • s.card := by
    rw [hc]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hnum : m * productGenerator I a (s.erase j) ^ n ∈ piece I ((n + k) • s.card) := by
    have h := SetLike.mul_mem_graded hm'
      (SetLike.pow_mem_graded n (productGenerator_mem I a (s.erase j)))
    simpa only [hdeg] using h
  let q : Chart I a s := HomogeneousLocalization.Away.mk (piece I)
    (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum
  have hmem : (ReesProductChart.chartBase I a s (a j).val) ^ n * q ∈
      (I ^ n).map (ReesProductChart.chartBase I a s) := by
    rw [chart_ordinaryPower_principal I a hj]
    exact Ideal.mul_mem_right q _ (Ideal.subset_span (by simp))
  refine ⟨⟨(ReesProductChart.chartBase I a s (a j).val) ^ n * q, hmem⟩, ?_⟩
  change ReesProductChart.chartMap I a s
    ((ReesProductChart.chartBase I a s (a j).val) ^ n * q) =
      localizationEvaluation I a s z.val
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [hrep, localizationEvaluation_fraction, map_mul, hmap]
  change algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) *
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum) = _
  rw [ReesProductChart.chartMap_mk, map_mul, (evaluation I).map_pow, evaluation_productGenerator,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_of_eq
  change coefficientProduct I a s ^ (n + k) * evaluation I m =
    coefficientProduct I a s ^ k * ((a j).val ^ n *
      (evaluation I m * coefficientProduct I a (s.erase j) ^ n))
  rw [pow_add, coefficientProduct_eq_pivot I a hj, mul_pow]
  ring

theorem chartPower_mem_pieceEvaluation (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    ∃ z : Piece I a s n,
      pieceEvaluation I a s n z = ReesProductChart.chartMap I a s q.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have hq : q.val ∈ Ideal.span {(ReesProductChart.chartBase I a s (a j).val) ^ n} :=
    (congrArg (fun K : Ideal (Chart I a s) => q.val ∈ K)
      (chart_ordinaryPower_principal I a hj n)).mp q.property
  rw [Ideal.mem_span_singleton] at hq
  obtain ⟨r, hr⟩ := hq
  obtain ⟨k, p, hp, hrep⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) r
  let m : reesAlgebra I := generator I (a j) ^ n * p
  have hm' : m ∈ piece I (n + k * s.card) := by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n (generator_mem I (a j))) hp
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_id, m] using h
  have hm : m ∈ integerPiece I ((n : ℤ) + (k : ℤ) * (s.card : ℤ)) := by
    have h : m ∈ integerPiece I (↑(n + k * s.card)) := hm'
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  let z : Piece I a s n := ⟨fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k,
      k, m, hm, rfl⟩
  refine ⟨z, ?_⟩
  change localizationEvaluation I a s (fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) = _
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [localizationEvaluation_fraction, hr, (ReesProductChart.chartMap I a s).map_mul,
    hmap, ← hrep, ReesProductChart.chartMap_mk,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  congr 1
  change evaluation I (generator I (a j) ^ n * p) = (a j).val ^ n * evaluation I p
  rw [map_mul, map_pow, evaluation_generator]

def chartPowerMap (n : ℕ) : Piece I a s n →+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) where
  toFun z := (pieceEvaluation_mem_chartPower I a hj n z).choose
  map_zero' := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [(pieceEvaluation_mem_chartPower I a hj n 0).choose_spec, map_zero]
    change 0 = ReesProductChart.chartMap I a s 0
    exact (map_zero _).symm
  map_add' z w := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    change ReesProductChart.chartMap I a s _ = ReesProductChart.chartMap I a s (_ + _)
    rw [(pieceEvaluation_mem_chartPower I a hj n (z+w)).choose_spec, map_add, map_add,
      (pieceEvaluation_mem_chartPower I a hj n z).choose_spec,
      (pieceEvaluation_mem_chartPower I a hj n w).choose_spec]

theorem chartPowerMap_evaluation (n : ℕ) (z : Piece I a s n) :
    ReesProductChart.chartMap I a s (chartPowerMap I a hj n z).val = pieceEvaluation I a s n z :=
  (pieceEvaluation_mem_chartPower I a hj n z).choose_spec

def chartPowerEquiv (n : ℕ) : Piece I a s n ≃+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) :=
  AddEquiv.ofBijective (chartPowerMap I a hj n) ⟨by
    intro z w hzw
    apply pieceEvaluation_injective I a s n
    rw [← chartPowerMap_evaluation I a hj n z, ← chartPowerMap_evaluation I a hj n w, hzw], by
    intro q
    obtain ⟨z, hz⟩ := chartPower_mem_pieceEvaluation I a hj n q
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [chartPowerMap_evaluation I a hj n z, hz]⟩

end
end PiExponent.ReesProductPower

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedPower
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenPower
noncomputable section
open PiExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem map_power_eq (n : ℕ) :
    ((I^n).map (base I a s)).map (coordinateEquiv I a s).toRingHom =
      (I^n).map (ReesProductChart.chartBase I a s) := by
  rw [Ideal.map_map]
  have he : (coordinateEquiv I a s).toRingHom.comp (base I a s) =
      ReesProductChart.chartBase I a s := by
    apply RingHom.ext
    intro r
    exact (coordinateEquiv I a s).apply_symm_apply _
  rw [he]

omit [Fintype J] [DecidableEq J] in
theorem coordinate_mem_power (n : ℕ) (x : ((I^n).map (base I a s))) :
    coordinateEquiv I a s x.val ∈ (I^n).map (ReesProductChart.chartBase I a s) := by
  have hx := Ideal.mem_map_of_mem
    (show coordinateRing I a s →+* ReesProductChart.Chart I a s from
      (coordinateEquiv I a s).toRingHom) x.property
  exact (congrArg (fun K : Ideal (ReesProductChart.Chart I a s) =>
    coordinateEquiv I a s x.val ∈ K) (map_power_eq I a s n)).mp hx

omit [Fintype J] [DecidableEq J] in
theorem inverse_map_power_eq (n : ℕ) :
    ((I^n).map (ReesProductChart.chartBase I a s)).map (coordinateEquiv I a s).symm.toRingHom =
      (I^n).map (base I a s) := by
  rw [Ideal.map_map]
  rfl

omit [Fintype J] [DecidableEq J] in
theorem inverse_mem_power (n : ℕ)
    (y : ((I^n).map (ReesProductChart.chartBase I a s))) :
    (coordinateEquiv I a s).symm y.val ∈ (I^n).map (base I a s) := by
  have hy := Ideal.mem_map_of_mem
    (show ReesProductChart.Chart I a s →+* coordinateRing I a s from
      (coordinateEquiv I a s).symm.toRingHom) y.property
  exact (congrArg (fun K : Ideal (coordinateRing I a s) =>
    (coordinateEquiv I a s).symm y.val ∈ K) (inverse_map_power_eq I a s n)).mp hy

def powerEquiv (n : ℕ) : ((I^n).map (base I a s)) ≃+
    ((I^n).map (ReesProductChart.chartBase I a s)) where
  toFun x := ⟨coordinateEquiv I a s x.val, coordinate_mem_power I a s n x⟩
  invFun y := ⟨(coordinateEquiv I a s).symm y.val, inverse_mem_power I a s n y⟩
  left_inv x := Subtype.ext ((coordinateEquiv I a s).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((coordinateEquiv I a s).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (coordinateEquiv I a s) x.val y.val)

omit [Fintype J] [DecidableEq J] in
@[simp] theorem powerEquiv_apply (n : ℕ) (z : ((I^n).map (base I a s))) :
    (powerEquiv I a s n z).val = coordinateEquiv I a s z.val := rfl

variable {s}

def pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ) :
    ReesLocalizedIntersections.Piece I a s n ≃+ ((I^n).map (base I a s)) :=
  (ReesProductPower.chartPowerEquiv I a hp n).trans (powerEquiv I a s n).symm

theorem coordinate_pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ)
    (z : ReesLocalizedIntersections.Piece I a s n) :
    coordinateEquiv I a s (pieceEquiv I a hp n z).val =
      (ReesProductPower.chartPowerMap I a hp n z).val := by
  change (powerEquiv I a s n (pieceEquiv I a hp n z)).val = _
  exact congrArg Subtype.val ((powerEquiv I a s n).apply_symm_apply _)

end
end PiExponent.ReesFrozenPower

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductRestriction
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] in
theorem productGenerator_factor {s t : Finset J} (hst : s ⊆ t) :
    productGenerator I a t = productGenerator I a s * productGenerator I a (t \ s) := by
  simp only [productGenerator_eq_prod]
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

def chartRestriction {s t : Finset J} (hst : s ⊆ t) : Chart I a s →+* Chart I a t :=
  HomogeneousLocalization.awayMap (piece I) (productGenerator_mem I a (t \ s))
    (productGenerator_factor I a hst)

theorem chartRestriction_base {s t : Finset J} (hst : s ⊆ t) (r : R) :
    chartRestriction I a hst (ReesProductChart.chartBase I a s r) =
      ReesProductChart.chartBase I a t r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

omit [Fintype J] [DecidableEq J] in
theorem chartMap_mk_homogeneous (s : Finset J) {d : ℕ}
    (hgen : productGenerator I a s ∈ piece I d) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • d)) :
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I) hgen k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [ReesProductChart.chartMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

omit [Fintype J] in
theorem coefficientRestriction_fraction {s t : Finset J} (hst : s ⊆ t) (r : R) (k : ℕ) :
    coefficientRestriction I a hst
      (IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) r
        (powerDenominator (coefficientProduct I a s) k)) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a t))
        (r * coefficientProduct I a (t \ s) ^ k)
        (powerDenominator (coefficientProduct I a t) k) := by
  have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
      (coefficientProduct I a s)) :=
    IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t)
      ⟨coefficientProduct I a (t \ s), coefficientProduct_factor I a hst⟩
  apply (hu.pow k).mul_right_injective
  calc
    _ = algebraMap R (Localization.Away (coefficientProduct I a t)) r := by
      have h := congrArg (coefficientRestriction I a hst)
        (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s)) r
          (powerDenominator (coefficientProduct I a s) k))
      simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow] using h
    _ = _ := by
      rw [← map_pow]
      dsimp only
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
      symm
      apply IsLocalization.mk'_eq_iff_eq_mul.mpr
      rw [← map_mul]
      congr 1
      change coefficientProduct I a s ^ k * (r * coefficientProduct I a (t \ s) ^ k) =
        r * coefficientProduct I a t ^ k
      rw [coefficientProduct_factor I a hst, mul_pow]
      ring

theorem chartMap_restriction {s t : Finset J} (hst : s ⊆ t) (q : Chart I a s) :
    ReesProductChart.chartMap I a t (chartRestriction I a hst q) =
      coefficientRestriction I a hst (ReesProductChart.chartMap I a s q) := by
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) q
  rw [chartRestriction, HomogeneousLocalization.awayMap_mk, chartMap_mk_homogeneous,
    ReesProductChart.chartMap_mk, coefficientRestriction_fraction,
    map_mul, (evaluation I).map_pow, evaluation_productGenerator]

theorem chartRestriction_power_mem {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    chartRestriction I a hst q.val ∈ (I ^ n).map (ReesProductChart.chartBase I a t) := by
  have hmap : ((I ^ n).map (ReesProductChart.chartBase I a s)).map (chartRestriction I a hst) =
      (I ^ n).map (ReesProductChart.chartBase I a t) := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    exact chartRestriction_base I a hst r
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ q.property

def chartPowerRestriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ) :
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) →+
      ↥((I ^ n).map (ReesProductChart.chartBase I a t)) where
  toFun q := ⟨chartRestriction I a hst q.val, chartRestriction_power_mem I a hst n q⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem chartPowerMap_restriction {s t : Finset J} {j k : J}
    (hj : j ∈ s) (hk : k ∈ t) (hst : s ⊆ t) (n : ℕ) (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartPowerMap I a hk n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      chartPowerRestriction I a hst n (chartPowerMap I a hj n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  apply ReesProductChart.chartMap_injective I a t
  change ReesProductChart.chartMap I a t _ =
    ReesProductChart.chartMap I a t (chartRestriction I a hst (chartPowerMap I a hj n z).val)
  rw [chartPowerMap_evaluation I a hk, chartMap_restriction, chartPowerMap_evaluation I a hj,
    pieceEvaluation_restriction]

end
end PiExponent.ReesProductRestriction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def restriction {s t : Finset J} (hst : s ⊆ t) : coordinateRing I a s →+* coordinateRing I a t :=
  (coordinateEquiv I a t).symm.toRingHom.comp
    ((ReesProductRestriction.chartRestriction I a hst).comp (coordinateEquiv I a s).toRingHom)

end
end PiExponent.ReesFrozenChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedPowerRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenPower
noncomputable section
open PiExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem pieceEquiv_restriction {s t : Finset J} {p r : J} (hp : p ∈ s) (hr : r ∈ t)
    (hst : s ⊆ t) (n : ℕ) (z : ReesLocalizedIntersections.Piece I a s n) :
    letI := ReesPolynomialPresentation.presentationAlgebra I a
    letI := ReesGradedModule.gradedScalarAction I a
    (pieceEquiv I a hr n (GradedCech.setRestriction
      (GradedPolynomialLaurent.grading (J := J) (R := R)) (ReesGradedModule.integerPiece I)
      MvPolynomial.X GradedPolynomialLaurent.variable_mem hst n z)).val =
      restriction I a hst (pieceEquiv I a hp n z).val := by
  let := ReesPolynomialPresentation.presentationAlgebra I a
  let := ReesGradedModule.gradedScalarAction I a
  apply (coordinateEquiv I a t).injective
  rw [coordinate_pieceEquiv, ReesProductRestriction.chartPowerMap_restriction I a hp hr hst n]
  change ReesProductRestriction.chartRestriction I a hst
    (ReesProductPower.chartPowerMap I a hp n z).val = _
  simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [coordinate_pieceEquiv]

end
end PiExponent.ReesFrozenPower

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductAugmentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductAugmentation
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def ordinaryFraction (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) : Piece I a s n := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ⟨fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
    (ordinaryPowerEquivIntegerPiece I n b).val 0,
      0, (ordinaryPowerEquivIntegerPiece I n b).val,
      by simpa only [Nat.cast_zero, zero_mul, add_zero] using
        (ordinaryPowerEquivIntegerPiece I n b).property, rfl⟩

end
end PiExponent.ReesProductAugmentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_RegularSectionChoice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def localCoefficientAddHom (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    GlobalSections X L.sheaf →+ Γ(U.toScheme, ⊤) where
  toFun s := coefficient e (restrictSection U.ι s)
  map_zero' := by
    exact (congrArg (coefficient e) (restrictSection_zero U.ι)).trans (coefficient_zero e)
  map_add' s t := by
    simp only [coefficient, restrictSection]
    erw [(Scheme.Modules.restrictFunctor U.ι).map_add (f := s) (g := t),
      Preadditive.comp_add, Preadditive.add_comp]
    rfl

def sectionLinearCombination (L : LineBundle X) {k : ℕ}
    (a : ℂ →+* Γ(X, ⊤)) (s : Fin k → GlobalSections X L.sheaf) (c : Fin k → ℂ) :
    GlobalSections X L.sheaf := ∑ j, scalarEnd (a (c j)) ≫ s j

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
attribute [local irreducible] affineBlowup projection exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  
attribute [local irreducible] PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] in
theorem tuple_mem (q : ℕ) (t : Fin (q + 1) → J) (k : Fin (q + 1)) : t k ∈ tupleSet t :=
  Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

omit [Fintype J] in
theorem tuple_nonempty (q : ℕ) (t : Fin (q + 1) → J) : (tupleSet t).Nonempty :=
  ⟨t 0, tuple_mem q t 0⟩

end
end PiExponent.ReesSheafCechBase

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_TupleCechBound
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TupleCechBound
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCechHigher
universe u
variable {J K A : Type*} [AddCommGroup A]

def FullSupport {q : ℕ} (c : Cochain J A q) : Prop :=
  ∀ t j, (∀ i, t i ≠ j) → c t = 0

def pullback (f : K → J) {q : ℕ} (c : Cochain J A q) : Cochain K A q :=
  fun t => c (f ∘ t)

def extend (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q) : Cochain J A q := by
  classical
  exact fun t => if h : ∀ i, t i ≠ p then c (fun i => ⟨t i, h i⟩) else 0

end
end PiExponent.TupleCechBound

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem fibre_nonconstant {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    ∃ i, x i ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i,hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp at hi
  | succ i => exact ⟨i,hi⟩

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AuxiliaryJetMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def literalJetSubstitution {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C (1 + Polynomial.X))
    (fun i => MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) + MvPolynomial.X i))

end PiExponent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_FormalAuxiliaryJet
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent

def formalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (c : Fin K → Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (FormalLogJet.formalJet (c ρ.1)).toLinearMap)

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def rectIndexEquiv (n : σ → ℕ) : RectIndex n ≃ (∀ i, Fin (n i)) where
  toFun d i := ⟨d.val i, d.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val), by
    intro i
    exact (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    exact Finsupp.ext fun i => rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

instance rectIndexFintype (n : σ → ℕ) : Fintype (RectIndex n) :=
  Fintype.ofEquiv (∀ i, Fin (n i)) (rectIndexEquiv n).symm

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_RectangularCotangent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentApprox.TransverseMultiplicity

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

abbrev RectangularRing (n : σ → ℕ) :=
  MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n

def rectangularAugmentationIdeal (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Ideal (RectangularRing (K := K) n) :=
  RingHom.ker (rectangularAugmentation (K := K) n (rectangularPositive n hn))

def unitRectIndex (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) (i : σ) : RectIndex n :=
  ⟨Finsupp.single i 1, by
    intro j
    by_cases h : j = i
    · subst j
      simpa using (show 1 < n i by have := hn i; omega)
    · simpa [Finsupp.single_eq_of_ne h] using rectangularPositive n hn j⟩

def rectangularFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    RectangularRing (K := K) n →ₗ[K] (σ → K) where
  toFun f i := rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i)
  map_add' f g := by ext i; exact congrFun (map_add (rectangularQuotientCoefficients (K := K) n) f g) _
  map_smul' a f := by ext i; exact congrFun (map_smul (rectangularQuotientCoefficients (K := K) n) a f) _

omit [Fintype σ] in
@[simp] theorem rectangularFirstCoefficients_mk (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : MvPowerSeries σ K) (i : σ) :
    rectangularFirstCoefficients (K := K) n hn (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) i =
      coeff (Finsupp.single i 1) f := rfl

def rectangularIdealFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    rectangularAugmentationIdeal (K := K) n hn →ₗ[K] (σ → K) :=
  (rectangularFirstCoefficients (K := K) n hn).comp
    ((rectangularAugmentationIdeal (K := K) n hn).subtype.restrictScalars K)

omit [Fintype σ] in
theorem rectangularIdealFirstCoefficients_mul (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f g : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularIdealFirstCoefficients (K := K) n hn (f * g) = 0 := by
  obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective f.val
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g.val
  have hFc : constantCoeff F = 0 := by
    have hf := f.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) f.val = 0 at hf
    simpa only [← hF, rectangularAugmentation_mk] using hf
  have hGc : constantCoeff G = 0 := by
    have hg := g.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) g.val = 0 at hg
    simpa only [← hG, rectangularAugmentation_mk] using hg
  ext i
  change rectangularFirstCoefficients (K := K) n hn (f.val * g.val) i = 0
  rw [← hF, ← hG, ← map_mul, rectangularFirstCoefficients_mk, firstCoeff_mul, hFc, hGc]
  simp

def rectangularCotangentFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    (rectangularAugmentationIdeal (K := K) n hn).Cotangent →ₗ[K] (σ → K) :=
  Ideal.Cotangent.lift (rectangularIdealFirstCoefficients (K := K) n hn)
    (rectangularIdealFirstCoefficients_mul n hn)

omit [Fintype σ] in
@[simp] theorem rectangularCotangentFirstCoefficients_toCotangent
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularCotangentFirstCoefficients (K := K) n hn
      ((rectangularAugmentationIdeal (K := K) n hn).toCotangent f) =
        rectangularFirstCoefficients (K := K) n hn f.val := rfl

end PiExponentApprox.TransverseMultiplicity

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_TranslatedPowerCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.RamifiedLocalLength.coverOriginIdeal_isMaximal _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TranslatedPowerCover

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

def decomposition (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Ring w a ≃ₗ[MvPolynomial σ k] ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (((toPolynomial w a).toAddEquiv.trans (PowerCover.decompositionAddEquiv w hw)).trans
    (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)).toLinearEquiv <| by
      intro p q
      have hsub : translatedPowerSubstitution w a p =
          PowerCover.powerSubstitution w (translationEquiv a p) := by
        rw [translatedPowerSubstitution_factor]
        rfl
      change (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)
          (PowerCover.decompositionAddEquiv w hw
            (translatedPowerSubstitution w a p * toPolynomial w a q)) = _
      rw [hsub, PowerCover.decompositionAddEquiv_power_mul]
      ext r
      simp [Finsupp.smul_apply, smul_eq_mul]

def basis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.Basis (∀ i, Fin (w i)) (MvPolynomial σ k) (Ring w a) where
  repr := decomposition w a hw

end
end PiExponent.TranslatedPowerCover

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RamifiedPowerLength
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.SeparablePointLength.pointLocalMap_isLocalHom _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.RamifiedLocalLength

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

def translatedPowerLocalBasis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.Basis (∀ i, Fin (w i)) (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) := by
  classical
  letI := translatedPowerLocalAlgebra w a hw
  let : (coverOriginIdeal w a).LiesOver (pointIdeal a) := coverOriginIdeal_liesOver w a hw
  letI := Localization.AtPrime.algebraOfLiesOver (pointIdeal a) (coverOriginIdeal w a)
  have hcomm : (coverOriginLocalEquiv w a).toRingHom.comp
        (algebraMap (Localization.AtPrime (pointIdeal a))
          (Localization.AtPrime (coverOriginIdeal w a))) =
      (translatedPowerLocalMap w a hw).toRingHom := by
    change (Localization.localRingHom (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).comp
        (Localization.localRingHom (pointIdeal a) (coverOriginIdeal w a)
          (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
          (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))) = _
    exact (Localization.localRingHom_comp (pointIdeal a) (coverOriginIdeal w a)
      (pointIdeal (0 : σ → k))
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
      (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).symm
  let e : Localization.AtPrime (coverOriginIdeal w a) ≃ₐ[Localization.AtPrime (pointIdeal a)]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
    { __ := coverOriginLocalEquiv w a
      commutes' := fun x => RingHom.congr_fun hcomm x }
  exact (basis_atPrime_of_unique_fibre (pointIdeal a) (coverOriginIdeal w a)
    (TranslatedPowerCover.basis w a hw) (coverOriginIdeal_unique w a hw)).map e.toLinearEquiv

end
end PiExponent.RamifiedLocalLength

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedChartRingEvaluation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.WeightedChartRingEvaluation
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponentSeshadri.Frames PiExponentSeshadri
open PiExponent.WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

variable {R ι σ : Type} [CommRing R]

abbrev ambientOpen (z : σ) : (ProjectiveO1.projectiveSpace R σ).Opens :=
  SectionOpens.isoOpen (ProjectiveO1.coordinateSection (R := R) z)

end
end PiExponent.WeightedChartRingEvaluation

end OAI
end


