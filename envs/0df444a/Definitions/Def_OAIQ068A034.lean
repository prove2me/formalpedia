-- Prove2me | Definitions.Def_OAIQ068A034
-- name    : OAIQ068A034
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:11:31.033662+00:00
-- url     : https://prove2.me/theorems/81bf377a-329c-443c-887f-d0f9b09fc50f
-- title:
--   Definitions bundle OAIQ068A034 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 5 declarations of OpenAI's Lean: 4 definitions and 1 theorem. The definitions and types are `OAI.PiExponent.GeometrySupport.CechOneConverse.schemeFreeOpen`, `OAI.PiExponent.ProjectiveTwistAcyclicity.schemeFreeOpen`, `OAI.PiExponentSeshadri.LineBundleFrameCocycle.isoOfCoordinateCoefficients`, `OAI.PiExponentSeshadri.Projective.coordinatePowerVertex`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: [`PiExponent_Approximation_CoordinateFrameIdentification`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateFrameIdentification.lean), [`PiExponent_Cohomology_CechOneConverse`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/CechOneConverse.lean), [`PiExponent_Cohomology_ProjectiveTwistAcyclicity`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveTwistAcyclicity.lean), [`PiExponent_Geometry_ProjectiveCoordinateChartMap`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateChartMap.lean), [`PiExponent_Geometry_ProjectiveCoordinateSections`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateSections.lean).
--
--   **Imports.** It imports the bundles `OAIQ068A019`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025` and `OAIQ068A027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A039`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A019
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022
import Definitions.Def_OAIQ068A023
import Definitions.Def_OAIQ068A024
import Definitions.Def_OAIQ068A025
import Definitions.Def_OAIQ068A027

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoordinateFrameIdentification
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

def isoOfCoordinateCoefficients (M N : X.Modules)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme)
    (f : ∀ i, N.restrict (U i).ι ≅ O (U i).toScheme)
    (s : ι → (O X ⟶ M)) (t : ι → (O X ⟶ N))
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s i)) = 1)
    (hcoeff : ∀ i j, coefficient (f i) (restrictSection (U i).ι (t j)) =
      coefficient (e i) (restrictSection (U i).ι (s j)))
    (hcover : ⊤ ≤ ⨆ i, U i) : M ≅ N := by
  have hnorm' (i : ι) : coefficient (f i) (restrictSection (U i).ι (t i)) = 1 :=
    (hcoeff i i).trans (hnorm i)
  have hc : ofFrames M U e = ofFrames N U f := by
    apply cocycle_ext
    funext i j W hi hj
    apply Units.ext
    change W.topIso.hom
      (frameChange (restrictOpenFrame hj (e j)) (restrictOpenFrame hi (e i)) : Γ(W.toScheme,⊤)) =
      W.topIso.hom
        (frameChange (restrictOpenFrame hj (f j)) (restrictOpenFrame hi (f i)) : Γ(W.toScheme,⊤))
    rw [frameChange_restrictOpenFrame hj hi (e j) (e i) (s j) (hnorm j),
      frameChange_restrictOpenFrame hj hi (f j) (f i) (t j) (hnorm' j), hcoeff i j]
  exact isoSheaf M U e hcover ≪≫ eqToIso (congrArg LineBundleGluing.sheaf hc) ≪≫
    (isoSheaf N U f hcover).symm

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOneConverse
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)

abbrev schemeFreeOpen (V : Y.Opens) : Y.Modules := freeOpen Y.ringCatSheaf V

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveTwistAcyclicity
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveTwistAcyclicity

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport.CechOne
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.ProjectiveTwistAcyclicity

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (O X ⟶ M)) (hc : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
include hf

variable [Fintype σ]

def coordinatePowerVertex (n : ℕ) (i : σ) :
    (schemeFreeOpen_p2 X (SectionOpens.isoOpen (s i)) ⟶ modulePow X M n) →+
      Laurent σ K n :=
  framedLaurentVertex _ (modulePow X M n) i n
    (coordinatePowerFrame (s i) n)
    (coordinateSectionRingEquiv M k s hc f hf i)

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateChartMap
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
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

lemma coordinateChartMap_ratio (i j : σ) :
    (coordinateChartMap k s hc i).appTop
      (PiExponent.ProjectiveO1.chartRatios (R := K) i j) =
    coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  let g := coordinateChartMap k s hc i
  let a := Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)
  have hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      (g ≫ a.hom) ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) := by
    simpa only [Proj.awayι, a, Category.assoc, Iso.hom_inv_id_assoc] using
      (coordinateChartMap_factor k s hc i).symm
  have h := sectionFrame_coordinate i k s hc (g ≫ a.hom) hg j
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    PiExponent.ProjectiveO1.coordinateOpen_pullback] at h
  change _ = g.appTop ((PiExponent.ProjectiveO1.coordinateOpen (R := K) i).topIso.inv
    (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (chartCoordinate (R := K) i j))) at h
  rw [PiExponent.ProjectiveO1.awayToSection_coordinate] at h
  exact h.symm

end
end PiExponentSeshadri.Projective

end OAI
end


