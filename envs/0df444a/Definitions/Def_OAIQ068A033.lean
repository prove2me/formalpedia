-- Prove2me | Definitions.Def_OAIQ068A033
-- name    : OAIQ068A033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:07:22.278055+00:00
-- url     : https://prove2.me/theorems/a770be1f-e191-4185-95e2-1e58c54cf107
-- title:
--   Definitions bundle OAIQ068A033 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 72 declarations of OpenAI's Lean: 37 definitions, 1 inductive type or structure, 6 instances and 28 theorems. The definitions and types are `OAI.PiExponent.GeometrySupport.FreeCechSections.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.TwistPresentations.coherentTwistFamily`, `OAI.PiExponent.GeometrySupport.TwistPresentations.presentationMiddle`, `OAI.PiExponent.GeometrySupport.TwistPresentations.presentationRight`, `OAI.PiExponent.GeometrySupport.TwistPresentations.twistShiftIso`, `OAI.PiExponent.GlobalPolynomialCoefficientLaw.CoefficientLaw`, `OAI.PiExponent.InvertibleIdealAway.pullbackIsoOfAvoids`, `OAI.PiExponent.NumericalAmpleness.cohomologyMap`, `OAI.PiExponent.PlaceCenteredBranch.ordinaryContact`, `OAI.PiExponent.ProjectiveGlobalPolynomials.coordinateChartPolynomial`, `OAI.PiExponent.ProjectiveGlobalPolynomials.representedRestriction`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Frame`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Law`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.Sections`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.chartOpen`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.frame`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.polynomial`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.CoordinateData.ringEquiv`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsicBundle`, `OAI.PiExponent.ProjectiveIntrinsicCoefficientLaw.intrinsicData`, `OAI.PiExponent.ProjectiveO1.globalSectionChartPolynomial`, `OAI.PiExponent.ProjectiveSectionExtension.globalPushEquiv`, `OAI.PiExponent.ProjectiveSectionExtension.quotientPowerRestriction`, `OAI.PiExponent.ReesFrozenChart.chart`, `OAI.PiExponent.ReesFrozenChart.chartOpen`, `OAI.PiExponent.ReesProductPowerSections.chartMorphism`, `OAI.PiExponent.ReesProductPowerSections.chartOpen`, `OAI.PiExponent.ReesSheafCechBase.chartMap`, `OAI.PiExponent.ReesSheafCechBase.freeOpenSectionsEquiv`, `OAI.PiExponent.ReesSheafCechBase.opens`, `OAI.PiExponent.ReesSheafCechBase.schemeFreeOpen`, `OAI.PiExponent.ReesSheafCechNaturality.schemeFreeOpen`, `OAI.PiExponent.WeightedChartRingEvaluation.ambientRingEquiv`, `OAI.PiExponent.WeightedChartRingEvaluation.chartFactor`, `OAI.PiExponentSeshadri.BlowupGluing.totalChart`, `OAI.PiExponentSeshadri.IdealModule.closedQuotientCongr`, `OAI.PiExponentSeshadri.IdealModule.closedQuotientRestrictIso`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_GlobalBlowupAffineSquare`, `PiExponent_Ampleness_GlobalExceptionalComparison`, `PiExponent_Ampleness_GlobalReesRecoveryComparison`, `PiExponent_Ampleness_ReesExceptionalSheaf`, `PiExponent_Ampleness_ReesFiniteCover`, `PiExponent_Ampleness_ReesFixedChart`, `PiExponent_Ampleness_ReesFixedRestriction`, `PiExponent_Ampleness_ReesProductSchemeChart`, `PiExponent_Ampleness_ReesProductSchemeRestriction`, `PiExponent_Approximation_TwistPresentations`, `PiExponent_Cohomology_FreeCechSections`, `PiExponent_Cohomology_NakaiCohomology`, `PiExponent_Cohomology_ReesCohomologySetup`, `PiExponent_Cohomology_ReesSheafCechBase`, `PiExponent_Cohomology_ReesSheafCechNaturality`, `PiExponent_Geometry_PlaceCenteredBranch`, `PiExponent_Geometry_ProjectiveGlobalPolynomials`, `PiExponent_Geometry_ProjectiveIntrinsicCoefficientLaw`, `PiExponent_Geometry_ProjectiveSectionExtension`, `PiExponent_Geometry_ProjectiveSectionPullback`, `PiExponent_Jets_PrimeTaylorCotangent`, `PiExponent_Jets_TransverseMultiplicity`, `PiExponent_LocalAlgebra_IdealModuleRestriction`, `PiExponent_LocalAlgebra_IdealPowerRestriction`, `PiExponent_LocalAlgebra_InvertibleIdealAway`, `PiExponent_LocalAlgebra_WeightedChartRingEvaluation`, `PiExponent_Polynomials_GlobalPolynomialCoefficientLaw`.
--
--   **Imports.** It imports the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025`, `OAIQ068A026` and `OAIQ068A027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A039`; the proofs of `OAI_PiExponent_BlowupCurveMargin_margin_of_image_outside_chart`, `OAI.PiExponent.BlowupCurveMargin.margin_of_image_outside_chart_q68`, `OAI_PiExponent_CurveDerivativeVanishing_ordinary_words_vanish`, `OAI.PiExponent.CurveDerivativeVanishing.ordinary_words_vanish_q68`, `OAI_PiExponent_CurveInequality_no_fibre_excess_of_constant_coordinate`, `OAI.PiExponent.CurveInequality.no_fibre_excess_of_constant_coordinate_q68`, `OAI_PiExponent_PersistentWeightComparison_ordinary_persistent_comparison`, `OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison_q68`, `OAI_PiExponent_TransverseSliceComparison_comparison_of_normal_basis` and `OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A020
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022
import Definitions.Def_OAIQ068A023
import Definitions.Def_OAIQ068A024
import Definitions.Def_OAIQ068A025
import Definitions.Def_OAIQ068A026
import Definitions.Def_OAIQ068A027

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalExceptionalComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

@[reassoc (attr := simp)] theorem affineRestrictionIso_hom_reesProjection :
    (affineRestrictionIso I U).hom ≫ ReesGrading.projection (affineCenterIdeal I U) =
      ((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom := by
  have h := congrArg (fun f => f ≫ U.1.toScheme.isoSpec.hom)
    (affineRestrictionIso_hom_projection I U)
  simpa only [AffineBlowup.projection, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupAffineSquare
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

def totalChart : ReesGrading.affineBlowup (affineCenterIdeal I U) ⟶ scheme I :=
  (affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι

instance totalChart_isOpenImmersion : IsOpenImmersion (totalChart I U) := by
  dsimp [totalChart]
  infer_instance

@[reassoc (attr := simp)] theorem totalChart_projection :
    totalChart I U ≫ projection I =
      ReesGrading.projection (affineCenterIdeal I U) ≫ baseChart U := by
  have he : (affineRestrictionIso I U).inv ≫ ((projection I) ∣_ U.1) =
      ReesGrading.projection (affineCenterIdeal I U) ≫ U.1.toScheme.isoSpec.inv := by
    apply (cancel_mono U.1.toScheme.isoSpec.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← affineRestrictionIso_hom_reesProjection I U, Iso.inv_hom_id_assoc]
  rw [totalChart, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, he,
    Category.assoc]
  rfl

@[simp] theorem baseChart_opensRange : (baseChart (X := X) U).opensRange = U.1 := by
  change (U.1.toScheme.isoSpec.inv ≫ U.1.ι).opensRange = U.1
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem totalChart_opensRange :
    (totalChart I U).opensRange = projection I ⁻¹ᵁ U.1 := by
  change ((affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem center_comap_baseChart :
    I.comap (baseChart U) = IdealPullback.specIdeal (affineCenterIdeal I U) := by
  rw [baseChart, Scheme.IdealSheafData.comap_comp, IdealPullback.comap_isoSpec_inv]

end
end PiExponentSeshadri.BlowupGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealModuleRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma closedModuleRestrictIso_naturality {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫ (closedModuleRestrictIso J f).hom =
      (closedModuleRestrictIso I f).hom ≫ closedMap (Scheme.IdealSheafData.comap_mono f h) := by
  apply (cancel_mono (closedInclusion (J.comap f))).mp
  simp only [Category.assoc, closedMap_inclusion]
  change (Scheme.Modules.restrictFunctor f).map (closedMap h) ≫
    restrictedToClosed J f ≫ closedInclusion (J.comap f) =
    restrictedToClosed I f ≫ closedInclusion (I.comap f)
  rw [restrictedToClosed_inclusion, restrictedToClosed_inclusion]
  unfold restrictedInclusion
  let F : Y.Modules ⥤ X.Modules := Scheme.Modules.restrictFunctor f
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun g : F.obj (closedModule I) ⟶ F.obj (unit Y) =>
      g ≫ (Scheme.Modules.restrictUnitIso f).hom)
      (F.map_comp (closedMap h) (closedInclusion J)).symm).trans
      (congrArg (fun g : closedModule I ⟶ unit Y =>
        F.map g ≫ (Scheme.Modules.restrictUnitIso f).hom) (closedMap_inclusion h)))

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalReesRecoveryComparison
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
open GeometrySupport

attribute [local irreducible] PiExponentSeshadri.BlowupGluing.affineRestrictionIso
  PiExponentSeshadri.ReesGrading.affineBlowup PiExponentSeshadri.ReesGrading.projection
  IdealPullbackMap.map IdealPullbackMap.comap

attribute [local instance] OAI.PiExponent.GlobalReesRecoveryComparison.affineChartNoetherian
instance affineProjection_quasiCompact {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    QuasiCompact (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) := by infer_instance

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesExceptionalSheaf
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.closedMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.powerMap_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedToClosed_isIso _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ReesGrading
noncomputable section
variable {R : Type} [CommRing R] (I : Ideal R)

theorem exceptionalLineBundle_sheaf_eq :
    (exceptionalLineBundle I).sheaf = IdealModule.closedModule (exceptionalIdeal I) := rfl

end
end PiExponentSeshadri.ReesGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFiniteCover
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace PiExponent.ReesFiniteCover
open PiExponentSeshadri.ReesGrading
variable {R J : Type} [CommRing R] (I : Ideal R) (a : J → I)
variable (ha : Ideal.span (Set.range fun j => (a j).val) = I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)
include ha

theorem iSup_generator_opensRange :
    (⨆ j, ((chartCover I).f (a j)).opensRange) = ⊤ := by
  have h j : ((chartCover I).f (a j)).opensRange =
      Proj.basicOpen (piece I) (generator I (a j)) :=
    Proj.opensRange_awayι (piece I) _ (generator_mem I (a j)) (by decide)
  simp_rw [h]
  exact iSup_generator_basicOpen I a ha

end PiExponent.ReesFiniteCover
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductSchemeChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem exists_chartMorphism :
    ∃ j : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I,
      j = Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  ⟨_, rfl⟩

def chartMorphism : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I :=
  (exists_chartMorphism I a hs).choose

theorem chartMorphism_eq :
    chartMorphism I a hs =
      Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  (exists_chartMorphism I a hs).choose_spec

instance chartMorphism_open : IsOpenImmersion (chartMorphism I a hs) := by
  rw [chartMorphism_eq]
  exact inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := s.card) (piece I) (productGenerator I a s)
      (productGenerator_mem I a s) (Finset.card_pos.mpr hs)))

theorem chartMorphism_projection :
    chartMorphism I a hs ≫ projection I =
      Spec.map (CommRingCat.ofHom (ReesProductChart.chartBase I a s)) := by
  rw [chartMorphism_eq]
  change Proj.awayι (piece I) (productGenerator I a s) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

local instance instIsOpenImmersionFChartCover (q : I) : IsOpenImmersion ((chartCover I).f q) :=
  (chartCover I).map_prop q

theorem chartMorphism_opensRange :
    (chartMorphism I a hs).opensRange =
      s.inf (fun j => ((chartCover I).f (a j)).opensRange) := by
  have he : (chartMorphism I a hs).opensRange =
      (Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs)).opensRange := by
    apply SetLike.coe_injective
    simp only [Scheme.Hom.coe_opensRange]
    rw [chartMorphism_eq]
    rfl
  rw [he]
  change (Proj.awayι (piece I) (productGenerator I a s) _ _).opensRange = _
  rw [Proj.opensRange_awayι, productGenerator_eq_prod]
  have h : ∀ t : Finset J,
      Proj.basicOpen (piece I) (∏ j ∈ t, generator I (a j)) =
      t.inf (fun j => Proj.basicOpen (piece I) (generator I (a j))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih => rw [Finset.prod_insert hj, Proj.basicOpen_mul, ih, Finset.inf_insert]
  rw [h]
  congr 1
  funext j
  exact (Proj.opensRange_awayι (piece I) (generator I (a j))
    (generator_mem I (a j)) (by decide)).symm

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chartMorphism I a hs).opensRange, isAffineOpen_opensRange _⟩

variable {p : J} (hp : p ∈ s)

include hp in
theorem exceptional_chart :
    ((exceptionalIdeal I).comap (chartMorphism I a hs)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {chartEquation I a (s := s) (p := p)} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartMorphism_projection,
    PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top,
    ReesProductChart.map_ideal_principal I a hp, Ideal.map_span, Set.image_singleton]
  rfl

end PiExponent.ReesProductPowerSections
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedChart
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

variable {s} (hs : s.Nonempty)
def chart : Spec (coordinateRing I a s) ⟶ affineBlowup I :=
  Spec.map (coordinateInv I a s) ≫
    ReesProductPowerSections.chartMorphism I a hs

attribute [local instance] OAI.PiExponent.ReesFrozenChart.coordinateSpec_isIso
instance instIsOpenImmersionChart : IsOpenImmersion (chart I a hs) := by
  exact IsOpenImmersion.comp _ _

theorem chart_projection :
    chart I a hs ≫ projection I = Spec.map (CommRingCat.ofHom (base I a s)) := by
  rw [chart, Category.assoc, ReesProductPowerSections.chartMorphism_projection]
  exact (Spec.map_comp
    (show CommRingCat.of R ⟶ CommRingCat.of (Chart I a s) from
      CommRingCat.ofHom (ReesProductChart.chartBase I a s))
    (coordinateInv I a s)).symm

theorem chart_opensRange :
    (chart I a hs).opensRange = (ReesProductPowerSections.chartMorphism I a hs).opensRange :=
  Scheme.Hom.opensRange_comp_of_isIso _ _

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chart I a hs).opensRange, isAffineOpen_opensRange _⟩

theorem chartOpen_eq :
    (chartOpen I a hs).1 = (ReesProductPowerSections.chartOpen I a hs).1 :=
  chart_opensRange I a hs

end
end PiExponent.ReesFrozenChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesProductSchemeRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesFrozenChart.coordinateInv_isIso _root_.OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesProductSchemeRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart PiExponent.ReesProductRestriction
open PiExponent.ReesProductPowerSections
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem chartRestriction_chartMorphism {s t : Finset J} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (chartRestriction I a hst)) ≫ chartMorphism I a hs =
      chartMorphism I a ht := by
  have h := Proj.SpecMap_awayMap_awayι (piece I)
    (productGenerator_mem I a s) (Finset.card_pos.mpr hs)
    (productGenerator_mem I a (t \ s)) (productGenerator_factor I a hst)
  rw [chartMorphism_eq, chartMorphism_eq]
  unfold chartRestriction
  simpa only [Proj.awayι, Proj.basicOpenIsoSpec, affineBlowup] using h

end
end PiExponent.ReesProductSchemeRestriction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesFixedRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

theorem restriction_chart {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (restriction I a hst)) ≫ chart I a hs = chart I a ht := by
  have he : (restriction I a hst).comp (coordinateEquiv I a s).symm.toRingHom =
      (coordinateEquiv I a t).symm.toRingHom.comp (ReesProductRestriction.chartRestriction I a hst) := by
    apply RingHom.ext
    intro z
    simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have heCat :
      (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
        CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) ≫
        CommRingCat.ofHom (restriction I a hst) =
      (CommRingCat.ofHom (ReesProductRestriction.chartRestriction I a hst) :
        CommRingCat.of (Chart I a s) ⟶ CommRingCat.of (Chart I a t)) ≫
        CommRingCat.ofHom (coordinateEquiv I a t).symm.toRingHom :=
    congrArg (fun f : Chart I a s →+* coordinateRing I a t => CommRingCat.ofHom f) he
  rw [chart, ← Category.assoc, ← Spec.map_comp]
  erw [heCat]
  rw [Spec.map_comp, Category.assoc,
    ReesProductSchemeRestriction.chartRestriction_chartMorphism I a hs ht hst]
  rfl

end
end PiExponent.ReesFrozenChart

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistPresentations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

def twistShiftIso (L : LineBundle X) (M : X.Modules) (n0 n : ℕ) :
    (moduleTwistFunctor L n).obj ((moduleTwistFunctor L n0).obj M) ≅
      (moduleTwistFunctor L (n0+n)).obj M :=
  eqToIso (by rw [moduleTwistFunctor_add]; rfl)

variable (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections)

abbrev presentationMiddle (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj (SheafOfModules.free s.I)

def presentationRight (n : ℕ) :
    presentationMiddle L s n ⟶ (moduleTwistFunctor L (n0+n)).obj M :=
  (moduleTwistFunctor L n).map s.π ≫ (twistShiftIso L M n0 n).hom

def coherentTwistFamily (L : LineBundle X)
    (M : {M : X.Modules // M.IsFinitePresentation}) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj M.val

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechHigher FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

abbrev schemeFreeOpen (Y : AlgebraicGeometry.Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_NakaiCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cohomologyMap (p : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars p)
    let _ := Module.compHom (cohomology N n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars p)
  letI := Module.compHom (cohomology N n) (baseScalars p)
  let g := (Ext.mk₀ f).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (baseScalars p r) x }

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesCohomologySetup
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesFrozenChart.instIsOpenImmersionChart _root_.OAI.PiExponent.ReesProductPowerSections.chartMorphism_open _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesCohomologySetup
noncomputable section
open AlgebraicGeometry PiExponentSeshadri.ReesGrading
variable {R : Type} [CommRing R] (I : Ideal R)

instance instIsNoetherianAffineBlowupOfIsNoetherianRing [IsNoetherianRing R] : IsNoetherian (affineBlowup I) := by
  let : CompactSpace (affineBlowup I) :=
    QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian (projection I) }

end
end PiExponent.ReesCohomologySetup

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechBase
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlobalReesRecoveryComparison.affineProjection_quasiCompact _root_.OAI.PiExponent.ReesCohomologySetup.instIsNoetherianAffineBlowupOfIsNoetherianRing _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.BlowupGluing.totalChart_isOpenImmersion _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.projection_separated _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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
  
attribute [local irreducible] PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def opens (j : J) : (affineBlowup I).Opens := ((chartCover I).f (a j)).opensRange

def freeOpenSectionsEquiv {X : Scheme} (U : X.Opens) (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with map_add' := fun _ _ => rfl }

theorem tupleOpen_eq (q : ℕ) (t : Fin (q + 1) → J) :
    (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).1 =
      CechHigher.intersection (opens I a) t := by
  change (chartMap I a (tuple_nonempty q t)).opensRange = _
  rw [ReesFrozenChart.chart_opensRange, ReesProductPowerSections.chartMorphism_opensRange]
  apply le_antisymm
  · apply le_iInf
    intro k
    exact Finset.inf_le (tuple_mem q t k)
  · apply Finset.le_inf
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact iInf_le (fun i => opens I a (t i)) k

end
end PiExponent.ReesSheafCechBase

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ReesSheafCechNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ReesSheafCechNaturality
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
open PiExponent.ReesSheafCechBase PiExponent.ReesFrozenChart
open PiExponent.ReesFrozenPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  
attribute [local irreducible] PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

end
end PiExponent.ReesSheafCechNaturality

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceCenteredBranch
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

def ordinaryContact {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) : ℚ :=
  OrdinaryDVRBranchJet.contact v c (lift p z c hc) (lift_nonconstant p z c hc hnc)

end PiExponent.PlaceCenteredBranch

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveGlobalPolynomials
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveGlobalPolynomials
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open GeometrySupport ProjectiveMonomialCech

variable {X : Scheme.{0}} {σ R : Type} [CommRing R] [Fintype σ]
variable {U : σ → X.Opens} {M : X.Modules} {n : ℕ}

def representedRestriction (V : X.Opens) (N : X.Modules) (b : structureSheaf X ⟶ N) :
    freeOpen X.ringCatSheaf V ⟶ N :=
  freeOpenMap X.ringCatSheaf (homOfLE (show V ≤ ⊤ from le_top)) ≫
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf).hom ≫ b

open PiExponentSeshadri.Projective PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open GeometrySupport.ProjectiveTupleCharts
open GeometrySupport.ProjectiveLaurentVertex GeometrySupport.ProjectiveGlobalPolynomialAlgebra
attribute [local instance] MvPolynomial.gradedAlgebra
variable (L : X.Modules) (s : σ → (structureSheaf X ⟶ L)) (k : R →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade R σ)) (hf : sectionsMorphism k s hc = f.hom)

def coordinateChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf X ⟶ modulePow X L n) : MvPolynomial (ChartVariables i) R :=
  framedHomRingEquiv (PiExponentSeshadri.SectionOpens.isoOpen (s i)) (modulePow X L n)
    (coordinatePowerFrame (s i) n) (coordinateSectionRingEquiv L k s hc f hf i)
    (representedRestriction (PiExponentSeshadri.SectionOpens.isoOpen (s i)) _ b)


end
end PiExponent.ProjectiveGlobalPolynomials

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveGlobalPolynomials
attribute [local irreducible] lineBundle coordinateSection scalars sectionsMorphism
variable {R σ : Type} [CommRing R] [Fintype σ]

def globalSectionChartPolynomial (n : ℕ) (i : σ)
    (b : structureSheaf (projectiveSpace R σ) ⟶
      modulePow (projectiveSpace R σ) (lineBundle (R := R) (σ := σ)).sheaf n) :
    MvPolynomial (ChartVariables i) R :=
  coordinateChartPolynomial (X := projectiveSpace R σ) (R := R) (σ := σ)
    (lineBundle (R := R) (σ := σ)).sheaf (coordinateSection (R := R) (σ := σ))
    (scalars (R := R) (σ := σ)) (coordinateSection_cover (R := R) (σ := σ))
    (Iso.refl (projectiveSpace R σ))
    (coordinate_sectionsMorphism_identity (R := R) (σ := σ)) n i b

end
end PiExponent.ProjectiveO1

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedChartRingEvaluation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

def ambientRingEquiv (z : σ) :
    Γ(ProjectiveO1.projectiveSpace R σ, ambientOpen (R := R) z) ≃+*
      MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
    ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
    (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z

def chartFactor (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (_coordinate : ι → σ) (_hcoordinate : ∀ i, a (_coordinate i) = Finsupp.single i 1) :
    Spec (CommRingCat.of (MvPolynomial ι R)) ⟶ (ambientOpen (R := R) z).toScheme :=
  Spec.map (CommRingCat.ofHom
    (evalAway (𝒜 := PolyGrade R σ) (affineMonomialMap (R := R) a) (X z)
      (by simp [affineMonomialMap, hz]))) ≫
    (coordinateSectionChartIso (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
      ProjectiveO1.scalars ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover
      (Iso.refl _) ProjectiveO1.coordinate_sectionsMorphism_identity z).inv

end
end PiExponent.WeightedChartRingEvaluation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_GlobalPolynomialCoefficientLaw
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.GlobalPolynomialCoefficientLaw
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

def CoefficientLaw {Y : Scheme} {M : Y.Modules} {A : Type} [CommRing A]
    (V : Y.Opens) (e : M.restrict V.ι ≅ structureSheaf V.toScheme)
    (E : Γ(Y,V) ≃+* A) (P : (structureSheaf Y ⟶ M) → A) : Prop :=
  ∀ s, P s = E (V.topIso.hom (coefficient e (restrictSection V.ι s)))

end PiExponent.GlobalPolynomialCoefficientLaw
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveIntrinsicCoefficientLaw
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveIntrinsicCoefficientLaw
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.Projective
attribute [local instance] MvPolynomial.gradedAlgebra

structure CoordinateData (R σ : Type) [CommRing R] where
  scheme : Scheme.{0}
  sheaf : scheme.Modules
  sections : σ → (structureSheaf scheme ⟶ sheaf)
  scalars : R →+* Γ(scheme,⊤)
  cover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (sections i)) = ⊤
  projectiveIso : scheme ≅ Proj (PolyGrade R σ)
  projective_eq : sectionsMorphism scalars sections cover = projectiveIso.hom

namespace CoordinateData
variable {R σ : Type} [CommRing R] (D : CoordinateData R σ)

def chartOpen (z : σ) : D.scheme.Opens := PiExponentSeshadri.SectionOpens.isoOpen (D.sections z)

def Sections (n : ℕ) : Type := structureSheaf D.scheme ⟶ modulePow D.scheme D.sheaf n

def Frame (n : ℕ) (z : σ) : Type :=
  (modulePow D.scheme D.sheaf n).restrict (D.chartOpen z).ι ≅
    structureSheaf (D.chartOpen z).toScheme

def frame (n : ℕ) (z : σ) : D.Frame n z := coordinatePowerFrame (D.sections z) n

def ringEquiv (z : σ) : Γ(D.scheme,D.chartOpen z) ≃+* MvPolynomial (ChartVariables z) R :=
  coordinateSectionRingEquiv D.sheaf D.scalars D.sections D.cover D.projectiveIso D.projective_eq z

def polynomial (n : ℕ) (z : σ) : D.Sections n → MvPolynomial (ChartVariables z) R :=
  ProjectiveGlobalPolynomials.coordinateChartPolynomial D.sheaf D.sections D.scalars
    D.cover D.projectiveIso D.projective_eq n z

def Law (n : ℕ) (z : σ) : Prop :=
  GlobalPolynomialCoefficientLaw.CoefficientLaw (D.chartOpen z) (D.frame n z)
    (D.ringEquiv z) (D.polynomial n z)

end CoordinateData

attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateSection
  ProjectiveO1.scalars ProjectiveO1.coordinateCocycle sectionsMorphism
  CoordinateAtlas.morphism atlasOfFramedSections
  CoordinateData.chartOpen CoordinateData.Sections CoordinateData.Frame
  CoordinateData.frame CoordinateData.ringEquiv CoordinateData.polynomial CoordinateData.Law

variable {R σ : Type} [CommRing R]

def intrinsicData : CoordinateData R σ where
  scheme := ProjectiveO1.projectiveSpace R σ
  sheaf := (ProjectiveO1.lineBundle (R := R) (σ := σ)).sheaf
  sections := ProjectiveO1.coordinateSection
  scalars := ProjectiveO1.scalars
  cover := ProjectiveO1.coordinateSection_cover
  projectiveIso := Iso.refl (ProjectiveO1.projectiveSpace R σ)
  projective_eq := ProjectiveO1.coordinate_sectionsMorphism_identity

def intrinsicBundle : LineBundle (intrinsicData (R := R) (σ := σ)).scheme :=
  ProjectiveO1.lineBundle (R := R) (σ := σ)

@[simp] theorem intrinsicBundle_sheaf :
    (intrinsicBundle (R := R) (σ := σ)).sheaf = (intrinsicData (R := R) (σ := σ)).sheaf := rfl

attribute [local semireducible] CoordinateData.Sections CoordinateData.chartOpen
  CoordinateData.polynomial CoordinateData.ringEquiv

attribute [local irreducible] intrinsicData intrinsicBundle
  CoordinateData.Sections CoordinateData.chartOpen CoordinateData.polynomial CoordinateData.ringEquiv

end
end PiExponent.ProjectiveIntrinsicCoefficientLaw

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionExtension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveSectionExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open GeometrySupport

variable {X Y : Scheme.{0}}

def quotientPowerRestriction (L : LineBundle Y) (f : X ⟶ Y) (n : ℕ)
    (s : GlobalSections Y (modulePow Y L.sheaf n)) :
    GlobalSections Y ((moduleTwistFunctor L n).obj
      ((Scheme.Modules.pushforward f).obj (structureSheaf X))) :=
  s ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (PiExponentSeshadri.IdealModule.structureMap f)

end
end PiExponent.ProjectiveSectionExtension

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionPullback
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveSectionExtension
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X Y : Scheme.{0}}

def globalPushEquiv (f : X ⟶ Y) (M : X.Modules) :
    GlobalSections X M ≃ GlobalSections Y ((Scheme.Modules.pushforward f).obj M) :=
  Equiv.ofBijective (fun s => PiExponentSeshadri.IdealModule.structureMap f ≫
    (Scheme.Modules.pushforward f).map s)
    (ClosedImmersionSerreTransfer.globalHom_push_bijective f M)

end PiExponent.ProjectiveSectionExtension
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_TransverseMultiplicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

instance rectangularQuotientFinite (n : σ → ℕ) :
    Module.Finite K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  Module.Finite.equiv (rectangularQuotientEquiv n).symm

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_PrimeTaylorCotangent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open PiExponentApprox.TransverseMultiplicity MvPowerSeries

variable {C ι σ : Type*} [Field C] [CharZero C] [Fintype ι]
variable [Fintype σ] [DecidableEq σ]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

omit [Fintype ι] [Fintype σ] in
theorem primeRectangular_maps_maximal
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      (rectangularAugmentationIdeal (K := Q.ResidueField) n hn).comap
        (rectangularTaylorAlgHom n tau) := by
  apply rectangularTaylorAlgHom_maps_residueIdeal n (rectangularPositive n hn)
    tau (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero
  exact le_of_eq (IsLocalRing.ker_residue (R := Localization.AtPrime Q)).symm

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IdealPowerRestriction
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealModule
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

def closedQuotientRestrictIso {I J : Y.IdealSheafData} (h : I ≤ J)
    (f : X ⟶ Y) [IsOpenImmersion f] :
    (cokernel (closedMap h)).restrict f ≅
      cokernel (closedMap (Scheme.IdealSheafData.comap_mono f h)) :=
  PreservesCokernel.iso (Scheme.Modules.restrictFunctor f) (closedMap h) ≪≫
    cokernel.mapIso _ _ (closedModuleRestrictIso I f) (closedModuleRestrictIso J f)
      (closedModuleRestrictIso_naturality h f)

def closedQuotientCongr {I J I' J' : X.IdealSheafData} (h : I ≤ J) (h' : I' ≤ J')
    (hI : I = I') (hJ : J = J') : cokernel (closedMap h) ≅ cokernel (closedMap h') := by
  subst I'
  subst J'
  exact Iso.refl _

end
end PiExponentSeshadri.IdealModule

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_InvertibleIdealAway
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.InvertibleIdealAway
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.InvertibleLocal
variable {X B C : Scheme.{0}}

theorem restrictedInclusion_isIso_of_unit
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι)
    (U : B.Opens) (V : X.affineOpens) (hUV : U ≤ p ⁻¹ᵁ V.1)
    (hunit : (I.comap p).comap U.ι = ⊤) :
    IsIso (restrictedInclusion J ι U.ι) := by
  have : Mono ι := hJ.1
  let φ := restrictedInclusion J ι U.ι
  have : Mono φ := inferInstance
  apply PiExponentSeshadri.IdealModule.isIso_of_affine_app
  intro W
  have himage : ((φ.val.app (op W.1)).hom).range = ⊤ := by
    change ((restrictedInclusion J ι U.ι).val.app (op W.1)).hom.range = _
    rw [restricted_image_on_chart J ι hJ U.ι W V
      ((U.ι_image_le W.1).trans hUV), hunit]
    rfl
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · have : Mono φ.val := inferInstanceAs
      (Mono ((Scheme.Modules.toPresheafOfModules U.toScheme).map φ))
    exact PresheafOfModules.injective_of_mono φ.val (op W.1)
  · intro r
    have hr : r ∈ ((φ.val.app (op W.1)).hom).range := by
      rw [himage]
      trivial
    exact hr

theorem inclusion_isIso_of_comap_top
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (hunit : I.comap p = ⊤) : IsIso ι := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro b
  obtain ⟨V, hV, hbV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show p b ∈ (⊤ : X.Opens) from trivial)
  let U := p ⁻¹ᵁ V
  have hi : IsIso (restrictedInclusion J ι U.ι) :=
    restrictedInclusion_isIso_of_unit I p J ι hJ U ⟨V, hV⟩ le_rfl (by
      rw [hunit, Scheme.IdealSheafData.comap_top])
  refine ⟨U, hbV, ?_⟩
  exact isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
    (Scheme.Modules.restrictUnitIso U.ι) hi

theorem pullback_inclusion_isIso_of_avoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    IsIso ((Scheme.Modules.pullback g).map ι) := by
  let V : X.Opens := ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩
  let U : B.Opens := p ⁻¹ᵁ V
  have hunit : I.comap (U.ι ≫ p) = ⊤ :=
    CompactJetIdeal.restrict_eq_top_of_disjoint I (U.ι ≫ p) (fun u => u.property)
  have hpresent := presents_restrict_general I p J ι hJ U.ι
  have hinc : IsIso (restrictedInclusion J ι U.ι) :=
    inclusion_isIso_of_comap_top I (U.ι ≫ p) (restrictLineBundle J U.ι)
      (restrictedInclusion J ι U.ι) hpresent hunit
  have : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ι) :=
    isIso_of_comp_iso_hom ((Scheme.Modules.restrictFunctor U.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.ι) hinc
  have hrange : Set.range g ⊆ Set.range U.ι := by
    rintro _ ⟨c, rfl⟩
    exact ⟨⟨g c, havoid c⟩, rfl⟩
  let h : C ⟶ U.toScheme := IsOpenImmersion.lift U.ι g hrange
  exact pullback_map_isIso_of_factors ι g U h (IsOpenImmersion.lift_fac _ _ _)

def pullbackIsoOfAvoids
    (I : X.IdealSheafData) (p : B ⟶ X)
    (J : LineBundle B) (ι : J.sheaf ⟶ structureSheaf B)
    (hJ : PresentsPullbackIdeal I p J ι) (g : C ⟶ B)
    (havoid : ∀ c, (g ≫ p) c ∉ I.support) :
    (J.pullback g).sheaf ≅ structureSheaf C := by
  exact @asIso C.Modules _ _ _ ((Scheme.Modules.pullback g).map ι)
    (pullback_inclusion_isIso_of_avoids I p J ι hJ g havoid) ≪≫ pullbackUnitIso g

end PiExponent.InvertibleIdealAway

end

end OAI
end


