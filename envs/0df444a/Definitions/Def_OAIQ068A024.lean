-- Prove2me | Definitions.Def_OAIQ068A024
-- name    : OAIQ068A024
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:56:34.890241+00:00
-- url     : https://prove2.me/theorems/936f0bd6-0e45-4735-8484-251948d06125
-- title:
--   Definitions bundle OAIQ068A024 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 68 declarations of OpenAI's Lean: 10 definitions, 4 instances and 54 theorems. The definitions and types are `OAI.PiExponent.ProjectiveLatticePullback.latticeCoordinates`, `OAI.PiExponent.ProjectiveLatticePullback.latticeProjectiveMap`, `OAI.PiExponent.ProjectiveLocalCoefficients.normalizedMap`, `OAI.PiExponent.WeightedLocalSheaf.generatedSection`, `OAI.PiExponentSeshadri.LineClosedUnit.frame`, `OAI.PiExponentSeshadri.LineClosedUnit.map`, `OAI.PiExponentSeshadri.Projective.chartOpenAlgebra`, `OAI.PiExponentSeshadri.Projective.coordinateFiniteTransition`, `OAI.PiExponentSeshadri.Projective.coordinateSectionChartIso`, `OAI.PiExponentSeshadri.Projective.coordinateSectionRingEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_ExceptionalCurveDegree`, `PiExponent_Approximation_ClosedPushforwardAffine`, `PiExponent_Approximation_ClosedPushforwardCoherent`, `PiExponent_Approximation_FrameSubopens`, `PiExponent_Approximation_LineClosedUnit`, `PiExponent_Approximation_SectionPowerFrames`, `PiExponent_Approximation_WeightedSectionOrder`, `PiExponent_Cohomology_ProjectiveLaurentVertex`, `PiExponent_Geometry_CurveModelFieldEmbedding`, `PiExponent_Geometry_PlaceValuationRing`, `PiExponent_Geometry_ProjectiveChartRingNaturality`, `PiExponent_Geometry_ProjectiveChartRingNaturalityCore`, `PiExponent_Geometry_ProjectiveChartSections`, `PiExponent_Geometry_ProjectiveCoordinateFiniteValues`, `PiExponent_Geometry_ProjectiveCoordinateRingNaturality`, `PiExponent_Geometry_ProjectiveCoordinateSections`, `PiExponent_Geometry_ProjectiveCoordinateValues`, `PiExponent_Geometry_ProjectiveLatticeOrder`, `PiExponent_Geometry_ProjectiveLatticePullback`, `PiExponent_Geometry_ProjectiveLocalCoefficients`, `PiExponent_Geometry_ProjectiveSpaceBasics`, `PiExponent_Geometry_ProjectiveTupleCharts`, `PiExponent_Geometry_WeightedLocalSheaf`, `PiExponent_LocalAlgebra_WeightedLocalLattice`, `PiExponent_Polynomials_WeightedMonomialPole`.
--
--   **Imports.** It imports the bundles `OAIQ068A012`, `OAIQ068A013`, `OAIQ068A014`, `OAIQ068A015` and `OAIQ068A016` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A031`, `OAIQ068A032`, `OAIQ068A033` and `OAIQ068A034`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013
import Definitions.Def_OAIQ068A014
import Definitions.Def_OAIQ068A015
import Definitions.Def_OAIQ068A016

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameSubopens
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

lemma frameChange_restrictOpenFrame {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ O U.toScheme) (f : M.restrict V.ι ≅ O V.toScheme)
    (s : O X ⟶ M) (hs : coefficient e (restrictSection U.ι s) = 1) :
    (frameChange (restrictOpenFrame hWU e) (restrictOpenFrame hWV f) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hWV).appTop (coefficient f (restrictSection V.ι s)) := by
  have h := coefficient_change (restrictOpenFrame hWU e) (restrictOpenFrame hWV f)
    (restrictSection W.ι s)
  rw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
    hs, map_one, mul_one] at h
  exact h.symm

end
end PiExponentSeshadri.Frames

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartRingNaturalityCore
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma away_chart_preimage_self :
    Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i) = ⊤ := by
  rw [← Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide)]
  exact Scheme.Hom.preimage_opensRange _

lemma away_chart_appLE_top :
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
      (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
      (by rw [away_chart_preimage_self]) =
    (Proj.basicOpen (PolyGrade R σ) (X i)).topIso.inv ≫
      (Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv.appTop := by
  change ((Proj.basicOpenIsoSpec (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).inv ≫
    (Proj.basicOpen (PolyGrade R σ) (X i)).ι).appLE _ _ _ = _
  rw [← Scheme.Hom.appLE_comp_appLE _ _ _ ⊤ ⊤
    (by simp) (by simp)]
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  congr 1

lemma awayToSection_pullback_top :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) ⊤
        (by rw [away_chart_preimage_self]) =
      (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv := by
  rw [away_chart_appLE_top]
  apply chartIso_pullback_top
  exact Proj.basicOpenToSpec_app_top (PolyGrade R σ) (X i)

local instance chartOpenAlgebra
    (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens) :
    Algebra (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra _ _

lemma awayToSection_pullback_open (V : (Spec (CommRingCat.of (PolyChart (R := R) i))).Opens)
    (hV : V ≤ Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide) ⁻¹ᵁ
      Proj.basicOpen (PolyGrade R σ) (X i)) :
    Proj.awayToSection (PolyGrade R σ) (X i) ≫
      (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE
        (Proj.basicOpen (PolyGrade R σ) (X i)) V hV =
      CommRingCat.ofHom (algebraMap (PolyChart (R := R) i) Γ(Spec (CommRingCat.of (PolyChart (R := R) i)),V)) := by
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := R) i))).inv ≫
    (Spec (CommRingCat.of (PolyChart (R := R) i))).presheaf.map (homOfLE le_top).op
  rw [← awayToSection_pullback_top (R := R) i, Category.assoc]
  congr 1

lemma chartFiniteSectionRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFiniteSectionRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ a := by
  classical
  let z := ∏ j ∈ s, chartCoordinate (R := R) i j
  let : Algebra (PolyChart (R := R) i)
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.openAlgebra _ _
  let : IsLocalization.Away z
      Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen _ _
  let E := IsLocalization.algEquiv (Submonoid.powers z)
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z)
    (Localization.Away z)
  change E ((relabeledSectionIso
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (Proj.basicOpen (PolyGrade R σ) (X i)) (PrimeSpectrum.basicOpen z)
    (Proj.opensRange_awayι _ _ (poly_X_mem i) (by decide))
    (coordinate_finset_preimage i s)).inv
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a))) = _
  rw [← E.commutes a]
  apply congrArg E
  erw [relabeledSectionIso_inv]
  change (Proj.awayToSection (PolyGrade R σ) (X i) ≫
    (Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op ≫
    (Proj.awayι (PolyGrade R σ) (X i) (poly_X_mem i) (by decide)).appLE _ _ _) a = _
  erw [Scheme.Hom.map_appLE]
  exact congrArg (fun f : CommRingCat.of (PolyChart (R := R) i) ⟶
    Γ(Spec (CommRingCat.of (PolyChart (R := R) i)), PrimeSpectrum.basicOpen z) => f a)
    (awayToSection_pullback_open i (PrimeSpectrum.basicOpen z) _)

attribute [local irreducible] chartFiniteSectionRingEquiv

lemma chartFinitePolynomialRingEquiv_restrict (s : Finset σ) (a : PolyChart (R := R) i) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) a)) =
      algebraMap _ _ (chartToPoly i a) := by
  rw [chartFinitePolynomialRingEquiv, RingEquiv.trans_apply, chartFiniteSectionRingEquiv_restrict]
  exact IsLocalization.ringEquivOfRingEquiv_eq _ _

lemma chartFinitePolynomialRingEquiv_restrict_poly (s : Finset σ)
    (p : MvPolynomial (ChartVariables i) R) :
    chartFinitePolynomialRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
  rw [chartFinitePolynomialRingEquiv_restrict]
  have h := RingHom.congr_fun (chartToPoly_comp_polyToChart (R := R) i) p
  change chartToPoly i (polyToChart i p) = p at h
  rw [h]

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartRingNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] AlgebraicGeometry.StructureSheaf.openAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma chartVariableOverlapRingEquiv_restrict (s : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) R) :
    chartVariableOverlapRingEquiv i s
      ((Proj (PolyGrade R σ)).presheaf.map (homOfLE inf_le_left).op
        (Proj.awayToSection (PolyGrade R σ) (X i) (polyToChart i p))) =
      algebraMap _ _ p := by
  classical
  have hprod : (∏ j ∈ s.image Subtype.val,
      chartToPoly (R := R) i (chartCoordinate i j)) =
      ∏ j ∈ s, (X j : MvPolynomial (ChartVariables i) R) := by
    rw [Finset.prod_image]
    · apply Finset.prod_congr rfl
      intro j hj
      simp [chartToPoly_coordinate, j.property]
    · intro a ha b hb hab
      exact Subtype.ext hab
  change relabeledOverlapEquiv
    (Proj.basicOpen (PolyGrade R σ) (X i))
    ((s.image Subtype.val).inf fun j => Proj.basicOpen (PolyGrade R σ) (X j))
    (s.inf fun j => Proj.basicOpen (PolyGrade R σ) (X j.val)) _ _
    (chartFinitePolynomialRingEquiv i (s.image Subtype.val)) hprod
    (by rw [Finset.inf_image]; rfl) _ = _
  apply relabeledOverlapEquiv_restrict
  exact chartFinitePolynomialRingEquiv_restrict_poly i (s.image Subtype.val) p

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateValues
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Projective
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] (i : σ)

lemma coordinatesMap_pullback_coordinate {Y : Scheme}
    (k : K →+* Γ(Y,⊤)) (a : σ → Γ(Y,⊤)) (hi : a i = 1)
    (g : Y ⟶ Spec (CommRingCat.of (PolyChart (R := K) i)))
    (heq : coordinatesMap Y k a i hi =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))
    (j : σ) :
    a j = ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  let F := evalAway (𝒜 := PolyGrade K σ) (eval₂Hom k a) (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : Γ(Y,⊤))))
  have hfactor : Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom F) = g := by
    apply (cancel_mono (Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide))).1
    simpa only [coordinatesMap, fromUnitCoordinate, Category.assoc] using heq
  have hf := congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
    Scheme.Hom.appTop g) hfactor
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop,
    ← Scheme.ΓSpecIso_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id] at hf
  have h := congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (chartCoordinate (R := K) i j)) hf
  change F (chartCoordinate (R := K) i j) = _ at h
  rw [evalAway_coordinate i k a hi j] at h
  exact h

lemma sectionFrame_coordinate {Y : Scheme} {M : Y.Modules}
    (k : K →+* Γ(Y,⊤)) (s : σ → (PiExponentSeshadri.Frames.O Y ⟶ M))
    (hc : (⨆ a, SectionOpens.isoOpen (s a)) = ⊤)
    (g : (SectionOpens.isoOpen (s i)).toScheme ⟶
      Spec (CommRingCat.of (PolyChart (R := K) i)))
    (hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      g ≫ Proj.awayι (PolyGrade K σ) (X i) (poly_X_mem i) (by decide)) (j : σ) :
    PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    ((Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      g.appTop).hom (chartCoordinate (R := K) i j) := by
  exact coordinatesMap_pullback_coordinate i
    ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
    (fun j => PiExponentSeshadri.Frames.coefficient (sectionFrame (s i))
      (PiExponentSeshadri.Frames.restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))
    (sectionFrame_normalized (s i)) g
    ((sectionsMorphism_local k s hc i).symm.trans hg) j

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionPowerFrames
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme} {M : X.Modules}

lemma coordinatePowerFrame_frameChange (si sj : structureSheaf X ⟶ M) (n : ℕ)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    (frameChange (restrictOpenFrame hi (coordinatePowerFrame si n))
      (restrictOpenFrame hj (coordinatePowerFrame sj n)) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hj).appTop
        (coefficient (PiExponentSeshadri.Projective.sectionFrame sj)
          (restrictSection (SectionOpens.isoOpen sj).ι si)) ^ n := by
  erw [frameChange_restrictOpenFrame hi hj _ _ (powerSection si n)
    (coordinatePowerFrame_normalized si n), coordinatePowerFrame_coefficient, map_pow]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveLaurentVertex
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex

section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_injective (i : ι) :
    Function.Injective (polynomialToGroupAlgebra (R := R) i) := by
  apply AddMonoidAlgebra.mapDomain_injective
  intro a b hab
  ext j
  exact Int.natCast_inj.mp (congrFun hab j)

omit [Fintype ι] in
theorem overlapToGroupAlgebra_injective (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapToGroupAlgebra (R := R) i s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (chartProduct (R := R) i s)) (overlapToGroupAlgebra i s)).mpr
  intro x y
  constructor
  · exact congrArg _
  · intro h
    rw [overlapToGroupAlgebra_base, overlapToGroupAlgebra_base] at h
    exact congrArg _ (polynomialToGroupAlgebra_injective i h)

theorem overlapLaurent_injective (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i}) :
    Function.Injective (overlapLaurent (R := R) i d s) :=
  (groupAlgebraToLaurent i d).injective.comp (overlapToGroupAlgebra_injective i s)

omit [Fintype ι] in
@[simp] theorem productExponent_outside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : productExponent i s k = 0 := by
  classical
  simp only [productExponent, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hne : j ≠ k := fun h => hk (h ▸ hj)
  simp [natExponentHom, Ne.symm hne]

omit [Fintype ι] in
theorem polynomialToGroupAlgebra_nonnegative (i : ι)
    (p : MvPolynomial {j : ι // j ≠ i} R) (a : {j : ι // j ≠ i} → ℤ)
    (ha : (polynomialToGroupAlgebra i p).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) : 0 ≤ a k := by
  obtain ⟨b, rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero ha
  exact Int.natCast_nonneg _

omit [Fintype ι] in
theorem overlapToGroupAlgebra_nonnegative (i : ι) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s))
    (a : {j : ι // j ≠ i} → ℤ) (ha : (overlapToGroupAlgebra i s z).coeff a ≠ 0)
    (k : {j : ι // j ≠ i}) (hk : k ∉ s) : 0 ≤ a k := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (chartProduct (R := R) i s) z
  have h := congrArg (overlapToGroupAlgebra i s) hp
  simp only [map_mul, map_pow, overlapToGroupAlgebra_base,
    polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_pow, one_pow] at h
  have hc := congrArg (fun q : chartGroupAlgebra (R := R) i =>
    q.coeff (a + n • productExponent i s)) h
  simp only [AddMonoidAlgebra.coeff_mul_single_add, mul_one] at hc
  have hn := polynomialToGroupAlgebra_nonnegative i p (a + n • productExponent i s)
    (hc ▸ ha) k
  simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
    smul_zero, add_zero] using hn

theorem overlapLaurent_regular (i : ι) (d : ℤ) (s : Finset {j : ι // j ≠ i})
    (z : Localization.Away (chartProduct (R := R) i s)) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (overlapLaurent i d s z) := by
  intro a ha k hk
  by_cases hki : k = i
  · exact Or.inl hki
  · apply Or.inr
    by_contra hks
    have hn : (⟨k, hki⟩ : {j : ι // j ≠ i}) ∉ s := by
      intro hm
      exact hks ⟨⟨k, hki⟩, hm, rfl⟩
    change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) a ≠ 0 at ha
    rw [groupAlgebraToLaurent_coefficient] at ha
    exact not_lt_of_ge (overlapToGroupAlgebra_nonnegative i s z _ ha ⟨k, hki⟩ hn) hk

end

attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
variable {ι R : Type*} [Fintype ι] [CommRing R]

omit [Fintype ι] in
@[simp] theorem productExponent_inside (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) (hk : k ∈ s) : productExponent i s k = 1 := by
  classical
  simp [productExponent, Finset.sum_apply, natExponentHom, Finsupp.single_apply, hk]

theorem exists_cleared_exponent (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ (n : ℕ) (b : ChartExponent i), natExponentHom i b = a + n • productExponent i s := by
  classical
  let n : ℕ := ∑ j : {j : ι // j ≠ i}, (-a j).toNat
  have hnn : ∀ k, 0 ≤ a k + (n : ℤ) := by
    intro k
    have hn : (-a k).toNat ≤ n :=
      Finset.single_le_sum (fun j _ => Nat.zero_le ((-a j).toNat)) (Finset.mem_univ k)
    have hn' : ((-a k).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    omega
  have hnonneg : ∀ k, 0 ≤ (a + n • productExponent i s) k := by
    intro k
    by_cases hk : k ∈ s
    · simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul, productExponent_inside i s k hk] using hnn k
    · simpa only [Pi.add_apply, Pi.smul_apply, productExponent_outside i s k hk,
        smul_zero, add_zero] using ha k hk
  refine ⟨n, Finsupp.equivFunOnFinite.symm (fun k => ((a + n • productExponent i s) k).toNat), ?_⟩
  funext k
  exact Int.toNat_of_nonneg (hnonneg k)

theorem groupAlgebra_single_in_overlap_range (i : ι) (s : Finset {j : ι // j ≠ i})
    (a : {j : ι // j ≠ i} → ℤ) (r : R) (ha : ∀ k, k ∉ s → 0 ≤ a k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapToGroupAlgebra i s z = AddMonoidAlgebra.single a r := by
  classical
  obtain ⟨n, b, hb⟩ := exists_cleared_exponent i s a ha
  have hinv : polynomialToGroupAlgebra (R := R) i (chartProduct i s) *
      AddMonoidAlgebra.single (-productExponent i s) 1 = 1 := by
    rw [polynomialToGroupAlgebra_product, AddMonoidAlgebra.single_mul_single]
    simp only [add_neg_cancel, one_mul]
    rfl
  refine ⟨Localization.mk (MvPolynomial.monomial b r) ⟨(chartProduct i s)^n, n, rfl⟩, ?_⟩
  change Localization.awayLift (polynomialToGroupAlgebra i) (chartProduct i s)
    (isUnit_iff_exists_inv.mpr ⟨_, hinv⟩) _ = _
  rw [Localization.awayLift_mk (polynomialToGroupAlgebra i) (chartProduct i s)
    (MvPolynomial.monomial b r) (AddMonoidAlgebra.single (-productExponent i s) 1) hinv n]
  change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single b r) * _ = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow,
    AddMonoidAlgebra.single_mul_single, hb]
  simp

theorem laurent_single_in_overlap_range (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (a : Monomial ι d) (r : R)
    (ha : ∀ k : {j : ι // j ≠ i}, k ∉ s → 0 ≤ a.val k) :
    ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a r := by
  obtain ⟨z, hz⟩ := groupAlgebra_single_in_overlap_range i s (fun j => a.val j) r ha
  refine ⟨z, ?_⟩
  change groupAlgebraToLaurent i d (overlapToGroupAlgebra i s z) = _
  rw [hz]
  change (Finsupp.domCongr (fullExponentEquiv i d))
    (Finsupp.single ((fullExponentEquiv i d).symm a) r) = _
  simp

theorem overlapLaurent_surjective_regular (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ z : Localization.Away (chartProduct (R := R) i s), overlapLaurent i d s z = p := by
  classical
  have hs : ∀ a ∈ p.support, ∃ z : Localization.Away (chartProduct (R := R) i s),
      overlapLaurent i d s z = Finsupp.single a (p a) := by
    intro a ha
    apply laurent_single_in_overlap_range
    intro k hk
    by_contra hn
    have hmem := hp a (Finsupp.mem_support_iff.mp ha) k (lt_of_not_ge hn)
    rcases hmem with hmem | ⟨j, hj, heq⟩
    · exact k.property hmem
    · exact hk ((Subtype.ext heq) ▸ hj)
  choose z hz using hs
  refine ⟨∑ a ∈ p.support, if h : a ∈ p.support then z a h else 0, ?_⟩
  rw [map_sum]
  calc
    _ = ∑ a ∈ p.support, Finsupp.single a (p a) := by
      apply Finset.sum_congr rfl
      intro a ha
      simp only [dite_eq_left ha, hz]
    _ = p := p.sum_single
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveChartSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology

variable {X : Scheme} (U : X.Opens) (M : X.Modules)

open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {R ι : Type} [CommRing R] [Fintype ι] (i : ι) (d : ℤ)

theorem framedLaurentOverlap_injective (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s)) :
    Function.Injective (framedLaurentOverlap U M i d s e r) :=
  (overlapLaurent_injective i d s).comp (framedHomRingEquiv U M e r).injective

theorem framedLaurentOverlap_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (b : schemeFreeOpen_p0 X U ⟶ M) :
    RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i})))
      (framedLaurentOverlap U M i d s e r b) :=
  overlapLaurent_regular i d s _

theorem framedLaurentOverlap_surjective_regular (s : Finset {j : ι // j ≠ i})
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,U) ≃+* Localization.Away (chartProduct (R := R) i s))
    (p : Laurent ι R d)
    (hp : RegularOn ({i} ∪ (Subtype.val '' (s : Set {j : ι // j ≠ i}))) p) :
    ∃ b : schemeFreeOpen_p0 X U ⟶ M,
      framedLaurentOverlap U M i d s e r b = p := by
  obtain ⟨a, ha⟩ := overlapLaurent_surjective_regular i d s p hp
  refine ⟨(framedHomRingEquiv U M e r).symm a, ?_⟩
  change overlapLaurent i d s ((framedHomRingEquiv U M e r)
    ((framedHomRingEquiv U M e r).symm a)) = p
  rw [AddEquiv.apply_symm_apply, ha]

end PiExponentSeshadri.ProjectiveChartSections

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def coordinateSectionChartIso (i : σ) :
    (SectionOpens.isoOpen (s i)).toScheme ≅ Spec (CommRingCat.of (PolyChart (R := K) i)) :=
  X.isoOfEq (sectionOpen_eq_coordinate_preimage M k s hc f hf i) ≪≫
    f.hom.preimageIso (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i)) ≪≫
      Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)

lemma coordinateSectionChartIso_hom_away (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom ≫
      Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) =
    (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  rw [hf]
  simp only [coordinateSectionChartIso, Iso.trans_hom, Category.assoc, Proj.awayι,
    Iso.hom_inv_id_assoc, Scheme.Hom.preimageIso_hom_ι, Scheme.isoOfEq_hom_ι_assoc]

def coordinateSectionRingEquiv (i : σ) :
    Γ(X,SectionOpens.isoOpen (s i)) ≃+* MvPolynomial (ChartVariables i) K :=
  (SectionOpens.isoOpen (s i)).topIso.commRingCatIsoToRingEquiv.symm.trans
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).trans
      (polynomialChartEquiv i))

lemma coordinateSectionRingEquiv_coordinate (i j : σ) :
    coordinateSectionRingEquiv M k s hc f hf i
      ((SectionOpens.isoOpen (s i)).topIso.hom
        (coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))) =
      chartToPoly (R := K) i (chartCoordinate i j) := by
  have h := sectionFrame_coordinate i k s hc
    (coordinateSectionChartIso M k s hc f hf i).hom
    (coordinateSectionChartIso_hom_away M k s hc f hf i).symm j
  change coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) =
    (schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
      (chartCoordinate i j) at h
  simp only [coordinateSectionRingEquiv, RingEquiv.trans_apply, h]
  change (polynomialChartEquiv i)
    ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i))
      ((SectionOpens.isoOpen (s i)).topIso.inv
        ((SectionOpens.isoOpen (s i)).topIso.hom
          ((schemeIsoGammaEquiv (coordinateSectionChartIso M k s hc f hf i)).symm
            (chartCoordinate i j))))) = _
  rw [Iso.hom_inv_id_apply, RingEquiv.apply_symm_apply]
  rfl

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateRingNaturality
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri
namespace Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (k : K →+* Γ(X,⊤))
variable (s : σ → (PiExponentSeshadri.Frames.O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
lemma coordinateSectionChartIso_factor (i : σ) :
    (coordinateSectionChartIso M k s hc f hf i).hom =
      f.hom.resLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le ≫
      (Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)).hom := by
  apply (cancel_mono (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide))).1
  rw [coordinateSectionChartIso_hom_away, hf]
  simp only [Category.assoc, Proj.awayι, Iso.hom_inv_id_assoc,
    Scheme.Hom.resLE_comp_ι]
lemma coordinateSectionChartIso_pullback (i : σ) :
    (Scheme.ΓSpecIso (CommRingCat.of (PolyChart (R := K) i))).inv ≫
      (coordinateSectionChartIso M k s hc f hf i).hom.appTop ≫
        (SectionOpens.isoOpen (s i)).topIso.hom =
    Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) ≫
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le := by
  rw [coordinateSectionChartIso_factor, Scheme.Hom.comp_appTop]
  simp only [Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top,
    Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma coordinateSectionRingEquiv_symm (i : σ) (p : MvPolynomial (ChartVariables i) K) :
    (coordinateSectionRingEquiv M k s hc f hf i).symm p =
      f.hom.appLE (Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i))
        (SectionOpens.isoOpen (s i))
        (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p)) := by
  exact congrArg (fun g : CommRingCat.of (PolyChart (R := K) i) ⟶ _ =>
    g.hom (polyToChart i p)) (coordinateSectionChartIso_pullback M k s hc f hf i)

lemma coordinateFiniteRingEquiv_appLE (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(Proj (PolyGrade K σ),
      Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X i) ⊓
        a.inf (fun j => Proj.basicOpen (PolyGrade K σ) (MvPolynomial.X j.val)))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x) =
      chartVariableOverlapRingEquiv i a x := by
  change chartVariableOverlapRingEquiv i a
    (isoPreimageSectionRingEquiv f _
      (X.presheaf.map (eqToHom (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).symm).op
        (f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le x))) = _
  rw [isoPreimageSectionRingEquiv_appLE f _ _
    (coordinateFiniteOpen_eq_preimage M s k hc f hf i a)]

lemma coordinateFiniteRingEquiv_restrict (i : σ) (a : Finset (ChartVariables i))
    (p : MvPolynomial (ChartVariables i) K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((coordinateSectionRingEquiv M k s hc f hf i).symm p)) =
      algebraMap _ _ p := by
  rw [coordinateSectionRingEquiv_symm]
  have h : X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
      (f.hom.appLE _ _ (sectionOpen_eq_coordinate_preimage M k s hc f hf i).le
        (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) =
      f.hom.appLE _ _ (coordinateFiniteOpen_eq_preimage M s k hc f hf i a).le
        ((Proj (PolyGrade K σ)).presheaf.map (homOfLE inf_le_left).op
          (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (polyToChart i p))) := by
    exact appLE_restrict_comm f.hom inf_le_left inf_le_left _ _ _
  rw [h, coordinateFiniteRingEquiv_appLE, chartVariableOverlapRingEquiv_restrict]
  rfl

end

end Projective
end PiExponentSeshadri

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PlaceValuationRing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.PlaceValuationRing

open CurveValuationCenter WeightedCurveDegree

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

theorem valuation_eq_fractionAddValuation (p : NormalizedPlace F E) :
    p.valuation = CurveLocalOrder.fractionAddValuation (ring p) E := by
  apply DVRValuationUnique.eq_fractionAddValuation p.valuation
  · intro a
    exact a.property
  · intro a ha _
    exact p.valuation.toValuation.mem_maximalIdeal_iff.mp ha
  · exact p.normalized

end PiExponent.PlaceValuationRing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_WeightedLocalLattice
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.WeightedLocalLattice

theorem generatedLattice_eq_span_of_minimum
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, fractionAddValuation A K (y a) ≤ fractionAddValuation A K (y b)) :
    generatedLattice A y s = Submodule.span A {y a} := by
  have hva : fractionAddValuation A K (y a) ≠ ⊤ :=
    (AddValuation.top_iff _).not.mpr hya
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨b, hb, rfl⟩
    have hv : 0 ≤ fractionAddValuation A K (y b / y a) := by
      rw [AddValuation.map_div]
      calc
        0 = fractionAddValuation A K (y a) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hva).symm
        _ ≤ fractionAddValuation A K (y b) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top hva).monotone (hmin b hb)
    obtain ⟨c, hc⟩ := (exists_local_element_iff_nonnegative_order _).mpr hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    exact div_mul_cancel₀ _ hya
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Submodule.subset_span ⟨a, ha, rfl⟩

end PiExponent.WeightedLocalLattice

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardAffine
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedPushforwardAffine
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation
variable {X Y : Scheme.{0}}

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  have : RingHomSurjective σ := ⟨f.app_surjective ⊤ (isAffineOpen_top Y)⟩
  let ψ : Γ((Scheme.Modules.pushforward f).obj M,⊤) →ₛₗ[σ] Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := {
    toFun := fun x => x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact (ψ.finite_iff_of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩).mpr hfin

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

end
end PiExponent.ClosedPushforwardAffine

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardCoherent
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ClosedPushforward

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

open PiExponent.CoherentAffineFinite PiExponent.FiniteGlobalPresentation
open PiExponent.ClosedPushforwardAffine

instance pushforward_isFinitePresentation (f : X ⟶ Y) [IsClosedImmersion f]
    [IsLocallyNoetherian Y] (M : X.Modules) [M.IsFinitePresentation] :
    ((Scheme.Modules.pushforward f).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  have : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have hM := (locallyFinitelyGenerated_of_finitePresentation M).restrict (f ⁻¹ᵁ U.1).ι
  obtain ⟨P,hP⟩ := affine_pushforward_exists_finitePresentation (f ∣_ U.1)
    (M.restrict (f ⁻¹ᵁ U.1).ι) hM
  exact presentation_transport (Z := U.1.toScheme) (OpenBaseChange.iso f U.1 M).symm P hP

end PiExponentSeshadri.ClosedPushforward

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateFiniteValues
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_restrict_apply (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(X,SectionOpens.isoOpen (s i))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op x) =
      algebraMap _ _ (coordinateSectionRingEquiv M k s hc f hf i x) := by
  have h := coordinateFiniteRingEquiv_restrict M k s hc f hf i a
    (coordinateSectionRingEquiv M k s hc f hf i x)
  simpa only [RingEquiv.symm_apply_apply] using h

lemma coordinateFiniteRingEquiv_coordinate (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) := by
  rw [coordinateFiniteRingEquiv_restrict_apply, coordinateSectionRingEquiv_coordinate]

lemma coordinateFiniteRingEquiv_symm_X (i : σ) (a : Finset (ChartVariables i))
    (j : ChartVariables i) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.X (R := K) j)) =
      X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j.val)))) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_coordinate,
    chartToPoly_coordinate, dite_eq_right j.property]

def coordinateFiniteTransition (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    Localization.Away (chartProduct (R := K) i a) →+*
      Localization.Away (chartProduct (R := K) j b) :=
  (coordinateFiniteRingEquiv M s k hc f hf j b).toRingHom.comp
    ((X.presheaf.map (homOfLE h).op).hom.comp
      (coordinateFiniteRingEquiv M s k hc f hf i a).symm.toRingHom)

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveTupleCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

include hf in
omit [Fintype σ] in

theorem coordinateOpen_isAffine (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
  erw [sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide)).preimage f.hom

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSpaceBasics
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ProjectiveO1
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable (R σ : Type) [CommRing R]

instance projectiveSpace_noetherian [IsNoetherianRing R] [Finite σ] :
    IsNoetherian (projectiveSpace R σ) := by
  let : IsLocallyNoetherian (projectiveSpace R σ) :=
    LocallyOfFiniteType.isLocallyNoetherian (polynomialProjectiveProjection R σ)
  let : CompactSpace (projectiveSpace R σ) :=
    QuasiCompact.compactSpace_of_compactSpace (polynomialProjectiveProjection R σ)
  exact {}

instance projectiveSpace_separated [Finite σ] : (projectiveSpace R σ).IsSeparated := by
  constructor
  have h : IsSeparated (polynomialProjectiveProjection R σ ≫
      terminal.from (Spec (CommRingCat.of R))) := inferInstance
  simpa only [terminal.comp_from] using h

instance projectiveSpace_diagonal_affine [Finite σ] :
    IsAffineHom (pullback.diagonal (terminal.from (projectiveSpace R σ))) := by
  infer_instance

end
end PiExponent.ProjectiveO1

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_LineClosedUnit
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.IdealModule.closedInclusion_mono _root_.OAI.PiExponentSeshadri.IdealModule.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PiExponentSeshadri.LineClosedUnit
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def map (L : LineBundle Y) : L.sheaf ⟶
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf) :=
  (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app L.sheaf

def frame (L : LineBundle Y) (U : Y.Opens) (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj L.sheaf)).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (O (f ⁻¹ᵁ U).toScheme) :=
  OpenBaseChange.iso f U _ ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((OpenBaseChange.leftSquare f U).app L.sheaf).symm ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso (pullbackFrame (f ∣_ U) e)

lemma framed_map (L : LineBundle Y) (U : Y.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) :
    e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom = IdealModule.structureMap (f ∣_ U) := by
  dsimp only [map, IdealModule.structureMap]
  have hu := OpenBaseChange.unit_compatibility f U L.sheaf
  have hn := (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit_naturality e.hom
  have hb := pullbackUnit_adjunction (f ∣_ U)
  rw [Adjunction.homEquiv_unit] at hb
  dsimp only [frame, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [← Category.assoc]
  rw [Category.assoc e.inv, hu]
  simp only [Category.assoc]
  have hec : (OpenBaseChange.leftSquare f U).hom.app L.sheaf ≫
      ((OpenBaseChange.leftSquare f U).app L.sheaf).inv = 𝟙 _ :=
    ((OpenBaseChange.leftSquare f U).app L.sheaf).hom_inv_id
  rw [← Functor.map_comp_assoc, hec]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change e.inv ≫ (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app _ ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.pullback (f ∣_ U)).map e.hom ≫ (pullbackUnitIso (f ∣_ U)).hom) = _
  rw [Functor.map_comp]
  have hn' := congrArg (fun t => e.inv ≫ t ≫
    (Scheme.Modules.pushforward (f ∣_ U)).map (pullbackUnitIso (f ∣_ U)).hom) hn
  simp only [Category.assoc, hb] at hn'
  exact hn'.trans (e.inv_hom_id_assoc _)

theorem epi [IsClosedImmersion f] (L : LineBundle Y) : Epi (map f L) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro y
  obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne y
  refine ⟨U,hy,?_⟩
  have hg : Epi (IdealModule.structureMap (f ∣_ U)) := IdealModule.structureMap_epi _
  have he := framed_map f L U e
  have : Epi (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
    (frame f L U e).hom) := he.symm ▸ hg
  have h1 : Epi ((Scheme.Modules.restrictFunctor U.ι).map (map f L) ≫
      (frame f L U e).hom) := epi_of_epi e.inv _
  exact (epi_comp_iff_of_isIso _ _).mp h1

end
end PiExponentSeshadri.LineClosedUnit

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveModelFieldEmbedding
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.CurveNormalizationModel.parameterChart_noetherian _root_.OAI.PiExponent.CurveValuationCenter.parameterValuationCenter_isPrime _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

theorem parameterLaurentChartFractionRing : IsFractionRing (parameterLaurentChart f hf) E := by
  let := parameterChartFractionRing f hf
  let : Algebra (parameterChart f hf) (parameterLaurentChart f hf) :=
    (parameterChartOverlapHom f hf).toAlgebra
  have : IsScalarTower (parameterChart f hf) (parameterLaurentChart f hf) E :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact isFractionRing_of_intermediate_domain (parameterChart f hf) E
    (parameterLaurentChart f hf) Subtype.val_injective

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ExceptionalCurveDegree
attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

theorem localIdeal_compactIdeal {A : Type} [CommRing A]
    {m : ℕ} {K : Type} [Fintype K] (c : K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : CompactLogJetIdeal.coordinateRing m →+* A) :
    localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (CompactLogJetIdeal.polynomialIdeal c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, CompactLogJetIdeal.restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

end
end PiExponent.ExceptionalCurveDegree

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedLocalSheaf
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
open PiExponent.WeightedLocalLattice
open scoped BigOperators
universe u

namespace PiExponent.WeightedLocalSheaf

def generatedSection
    {A K : Type u} {ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) :
    structureSheaf (Spec (CommRingCat.of A)) ⟶ generatedSheaf (A := A) y s :=
  tildeSelf.inv ≫ (tilde.functor (CommRingCat.of A)).map
    (ModuleCat.ofHom (generatedSectionMap y s a ha))

end PiExponent.WeightedLocalSheaf

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_WeightedMonomialPole
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
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

theorem coordinateOrder_le_realValuation (v : AddValuation K (WithTop ℤ)) (x : K) :
    ((coordinateOrder v x : ℝ) : WithTop ℝ) ≤ realValuation v x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [realValuation_of_ne_zero v x hx]

theorem realValuation_le_iff (v : AddValuation K (WithTop ℤ)) (x y : K) :
    realValuation v x ≤ realValuation v y ↔ v x ≤ v y :=
  (Int.cast_strictMono (R := ℝ)).withTop_map.le_iff_le

theorem coordinateOrder_pow (v : AddValuation K (WithTop ℤ))
    (x : K) (hx : x ≠ 0) (n : ℕ) :
    coordinateOrder v (x ^ n) = (n : ℤ) * coordinateOrder v x := by
  rw [coordinateOrder, dite_eq_right (pow_ne_zero n hx), coordinateOrder, dite_eq_right hx]
  have hu : Units.mk0 (x ^ n) (pow_ne_zero n hx) = (Units.mk0 x hx) ^ n := by
    apply Units.ext
    rfl
  rw [hu, integerOrder_pow]

end PiExponent.WeightedMonomialPole

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedSectionOrder
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.LocalSectionOrder PiExponent.CurveLocalOrder
open scoped BigOperators

namespace PiExponent.WeightedSectionOrder


variable {A K : Type} {ι : Type*} [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]

theorem coordinate_coefficient (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) =
      (coordinateBasis y s a ha hya hspan).symm
        ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ := by
  unfold localCoefficient coefficient coordinateFrame generatedSection
  erw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, ← Functor.map_comp_assoc]
  have h := coefficient_tilde_end
    ((coordinateBasis y s a ha hya hspan).symm.toLinearMap.comp
      (generatedSectionMap y s b hb))
  simp only [LinearMap.comp_apply] at h
  simp [generatedSectionMap] at h
  exact h

theorem coordinate_coefficient_image (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) :
    algebraMap A K (localCoefficient (coordinateFrame y s a ha hya hspan)
      (generatedSection y s b hb)) = y b / y a := by
  rw [coordinate_coefficient, eq_div_iff hya]
  have h := (coordinateBasis y s a ha hya hspan).apply_symm_apply
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩
  have hh := congrArg (fun z : generatedLattice A y s => (z : K)) h
  change (coordinateBasis y s a ha hya hspan).symm
    ⟨y b, Submodule.subset_span ⟨b, hb, rfl⟩⟩ • y a = y b at hh
  simpa only [Algebra.smul_def] using hh

theorem coordinate_coefficient_ne_zero (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s)
    (hya : y a ≠ 0) (hspan : generatedLattice A y s = Submodule.span A {y a})
    (b : ι) (hb : b ∈ s) (hyb : y b ≠ 0) :
    localCoefficient (coordinateFrame y s a ha hya hspan) (generatedSection y s b hb) ≠ 0 := by
  intro h
  have hr := coordinate_coefficient_image y s a ha hya hspan b hb
  rw [h, map_zero] at hr
  exact div_ne_zero hyb hya hr.symm

end PiExponent.WeightedSectionOrder

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLocalCoefficients
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.Projective PiExponentSeshadri.LineBundleGluing

namespace PiExponent.ProjectiveLocalCoefficients


variable {R A σ : Type} [CommRing R] [CommRing A]
attribute [local instance] MvPolynomial.gradedAlgebra

def normalizedMap (k : R →+* A) (z : σ → A) (i : σ) (hi : z i = 1) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  fromUnitCoordinate (eval₂Hom k z) (by decide) (poly_X_mem i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : A)))

end PiExponent.ProjectiveLocalCoefficients

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLatticePullback
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_diagonal_affine _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_noetherian _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_separated _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder

namespace PiExponent.ProjectiveLatticePullback


variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

def latticeCoordinates (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) (b : σ) : A :=
  localCoefficient (A := A) (coordinateFrame y Finset.univ a (Finset.mem_univ a) hya hspan)
    (generatedSection y Finset.univ b (Finset.mem_univ b))

theorem latticeCoordinates_self (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    latticeCoordinates y a hya hspan a = 1 := by
  apply IsFractionRing.injective A K
  rw [map_one]
  exact (coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
    a (Finset.mem_univ a)).trans (div_self hya)

def latticeProjectiveMap (k : R →+* A) (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a}) :
    Spec (CommRingCat.of A) ⟶ ProjectiveO1.projectiveSpace R σ :=
  ProjectiveLocalCoefficients.normalizedMap k (latticeCoordinates y a hya hspan) a
    (latticeCoordinates_self y a hya hspan)

end PiExponent.ProjectiveLatticePullback

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveLatticeOrder
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.WeightedLocalSheaf PiExponent.WeightedLocalLattice
open PiExponent.WeightedSectionOrder PiExponent.LocalSectionOrder
open PiExponent.ProjectiveLatticePullback PiExponent.CurveLocalOrder

namespace PiExponent.ProjectiveLatticeOrder

variable {R A K σ : Type} [CommRing R] [CommRing A] [IsDomain A]
  [IsDiscreteValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Fintype σ]

theorem latticeCoordinates_order (y : σ → K) (a : σ) (hya : y a ≠ 0)
    (hspan : generatedLattice A y Finset.univ = Submodule.span A {y a})
    (b : σ) (hyb : y b ≠ 0) :
    ((IsDiscreteValuationRing.addVal A (latticeCoordinates y a hya hspan b)).toNat : ℤ) =
      WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y b) -
        WeightedPolynomialPole.coordinateOrder (fractionAddValuation A K) (y a) := by
  let c : A := latticeCoordinates y a hya hspan b
  have hc : c ≠ 0 := coordinate_coefficient_ne_zero y Finset.univ a
    (Finset.mem_univ a) hya hspan b (Finset.mem_univ b) hyb
  have hi := integerOrder_field_image_eq_length (K := K) hc
  have hu : Units.mk0 (algebraMap A K c)
      ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hc) =
      Units.mk0 (y b) hyb / Units.mk0 (y a) hya := by
    apply Units.ext
    simp only [Units.val_div_eq_div_val, Units.val_mk0]
    exact coordinate_coefficient_image y Finset.univ a (Finset.mem_univ a) hya hspan
      b (Finset.mem_univ b)
  rw [hu, WeightedCurveDegree.integerOrder_div, length_quotient_span_eq_addVal hc] at hi
  simpa only [WeightedPolynomialPole.coordinateOrder, dite_eq_right hyb, dite_eq_right hya] using hi.symm

end PiExponent.ProjectiveLatticeOrder

end

end OAI
end


