-- Prove2me | Definitions.Def_OAIQ068A019
-- name    : OAIQ068A019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:49:51.44999+00:00
-- url     : https://prove2.me/theorems/371f9544-8ca7-4c47-8513-28bb1e983052
-- title:
--   Definitions bundle OAIQ068A019 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 67 declarations of OpenAI's Lean: 26 definitions, 3 instances and 38 theorems. The definitions and types are `OAI.PiExponentJets.W22.parentChildIncidenceEquiv`, `OAI.PiExponentJets.W25.cumulativeHomogeneousQuotientEquiv`, `OAI.PiExponentJets.W28.LocalIntersection.scalarKernelEquiv`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlong`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineDescentAlongPushforwardIso`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.affineSpecTopSections`, `OAI.PiExponentSeshadri.ClosedAnnihilatedDescent.closedDescentPushforwardIso`, `OAI.PiExponentSeshadri.Projective.schemeFreeOpen`, `OAI.PiExponentSiegel.W17.ConeLocalLength.ConeAway`, `OAI.PiExponentSiegel.W17.ConeLocalLength.LaurentChart`, `OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalConeAlgebra`, `OAI.PiExponentSiegel.W17.ConeLocalLength.affineLocalToConeLocal`, `OAI.PiExponentSiegel.W17.ConeLocalLength.affineToConeAway`, `OAI.PiExponentSiegel.W17.ConeLocalLength.awayChartPrime`, `OAI.PiExponentSiegel.W17.ConeLocalLength.coneAwayToLaurent`, `OAI.PiExponentSiegel.W17.ConeLocalLength.coneHomogenizingUnit`, `OAI.PiExponentSiegel.W17.ConeLocalLength.coneLaurentEquiv`, `OAI.PiExponentSiegel.W17.ConeLocalLength.coneLocalCoordinate`, `OAI.PiExponentSiegel.W17.ConeLocalLength.conePrime`, `OAI.PiExponentSiegel.W17.ConeLocalLength.conePrimeLocalizationEquiv`, `OAI.PiExponentSiegel.W17.ConeLocalLength.coneToLaurent`, `OAI.PiExponentSiegel.W17.ConeLocalLength.laurentToConeAway`, `OAI.PiExponentSiegelAux.W31.regularSequenceAugmentation`, `OAI.PiExponentSiegelAux.W31.regularSequenceResolution`, `OAI.PiExponentSiegelAux.W31.scalarConeTopDualCoordinate`, `OAI.PiExponentSiegelAux.W31.scalarConeTopEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Approximation_AffineClosedAnnihilatedDescent`, `PiExponent_Approximation_ClosedPullbackUnitRestriction`, `PiExponent_Approximation_CoordinateFrameIdentification`, `PiExponent_Approximation_GlobalClosedAnnihilatedDescent`, `PiExponent_Geometry_ProjectiveCoordinateSections`, `PiExponent_Jets_KoszulTopDifferential`, `PiExponent_LocalAlgebra_ConeComplex`, `PiExponent_LocalAlgebra_ConeLocalLength`, `PiExponent_LocalAlgebra_ConePrimeLocalization`, `PiExponent_LocalAlgebra_ConeQuotientAugmentation`, `PiExponent_LocalAlgebra_ConeRegularSequence`, `PiExponent_LocalAlgebra_CumulativeHilbertSections`, `PiExponent_LocalAlgebra_IteratedKoszulExactness`, `PiExponent_LocalAlgebra_KoszulFiniteFree`, `PiExponent_LocalAlgebra_KoszulTopTerm`, `PiExponent_LocalAlgebra_LocalIntersectionTransport`, `PiExponent_LocalAlgebra_LocalizationQuotientParameters`, `PiExponent_LocalAlgebra_NaturalMultiplicityPropagation`, `PiExponent_LocalAlgebra_RegularSequenceExt`, `PiExponent_LocalAlgebra_RegularSequenceResolution`, `PiExponent_Polynomials_HomogeneousQuotientDimension`.
--
--   **Imports.** It imports the bundles `OAIQ068A001`, `OAIQ068A002`, `OAIQ068A003`, `OAIQ068A006`, `OAIQ068A009`, `OAIQ068A010` and `OAIQ068A011` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ068A034`; the proofs of `OAI_PiExponentJets_PolynomialLocalResidueResolution_exists_regularParameters_actual_height`, `OAI.PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height_q68`, `OAI_PiExponentJets_W22_ActualRegularCutHistory_degree_bound`, `OAI.PiExponentJets.W22.ActualRegularCutHistory.degree_bound_q68`, `OAI_PiExponentJets_W22_RetainedPrimeCycle_retainedChild_dimension`, `OAI.PiExponentJets.W22.RetainedPrimeCycle.retainedChild_dimension_q68`, `OAI_PiExponentJets_W22_actualHP_natDegree_of_prime_dimension`, `OAI.PiExponentJets.W22.actualHP_natDegree_of_prime_dimension_q68`, `OAI_PiExponentJets_W22_affine_local_regular_list_bezout`, `OAI.PiExponentJets.W22.affine_local_regular_list_bezout_q68`, `OAI_PiExponentJets_W22_homogeneous_local_regular_bezout`, `OAI.PiExponentJets.W22.homogeneous_local_regular_bezout_q68`, `OAI_PiExponentJets_W24_polynomial_prime_pair_dimension`, `OAI.PiExponentJets.W24.polynomial_prime_pair_dimension_q68`, `OAI_PiExponentJets_W28_LocalIntersection_regular_ring_onecut_length`, `OAI.PiExponentJets.W28.LocalIntersection.regular_ring_onecut_length_q68`, `OAI_PiExponentSiegelAux_W30_iterateScalarCones_dual_low_exact`, `OAI.PiExponentSiegelAux.W30.iterateScalarCones_dual_low_exact_q68`, `OAI_PiExponentSiegel_W58_polynomialLocal_regular_prefix_maximal_not_associated`, `OAI.PiExponentSiegel.W58.polynomialLocal_regular_prefix_maximal_not_associated_q68`, `OAI_PiExponent_CurvePrimeHeight_kernel_height_le`, `OAI.PiExponent.CurvePrimeHeight.kernel_height_le_q68`, `OAI_PiExponent_CurvePrimeHeight_kernel_height_succ_le` and `OAI.PiExponent.CurvePrimeHeight.kernel_height_succ_le_q68`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003
import Definitions.Def_OAIQ068A006
import Definitions.Def_OAIQ068A009
import Definitions.Def_OAIQ068A010
import Definitions.Def_OAIQ068A011

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_AffineClosedAnnihilatedDescent
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {R S : CommRingCat.{0}}

variable {X Y : Scheme.{0}}

def affineSpecTopSections [IsAffine X] (M : X.Modules) :
    moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M) ≃ₗ[Γ(X,⊤)]
      Γ(M,⊤) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul
      ((X.toSpecΓ.app ⊤)
        ((Spec Γ(X,⊤)).presheaf.map (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op
          ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul r m
    apply congrArg (fun a : Γ(X,⊤) =>
      @SMul.smul Γ(X,⊤) Γ(M,⊤) (M.val.obj (op ⊤)).isModule.toSMul a m)
    have hi : (homOfLE (show (⊤ : (Spec Γ(X,⊤)).Opens) ≤ ⊤ from le_top)).op = 𝟙 _ := rfl
    rw [hi, CategoryTheory.Functor.map_id]
    change X.toSpecΓ.appTop ((Scheme.ΓSpecIso Γ(X,⊤)).inv r) = r
    rw [Scheme.toSpecΓ_appTop]
    exact (Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r

lemma affineSpecTopSections_annihilator [IsAffine X] (M : X.Modules) (I : Ideal Γ(X,⊤))
    (h : I ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    I ≤ Module.annihilator Γ(X,⊤)
      (moduleSpecΓFunctor.obj (PiExponent.GlobalSectionClearing.affineToSpecModule M)) := by
  intro r hr
  rw [Module.mem_annihilator] at *
  intro m
  apply (affineSpecTopSections M).injective
  rw [map_smul, map_zero]
  exact Module.mem_annihilator.mp (h hr) _

def affineDescentAlong [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules)
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) : Y.Modules :=
  (Scheme.Modules.pushforward Y.isoSpec.inv).obj
    (specSurjectiveDescent f.appTop hf
      (PiExponent.GlobalSectionClearing.affineToSpecModule M)
      (affineSpecTopSections_annihilator M _ h))

def affineDescentAlongPushforwardIso [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    (hf : Function.Surjective f.appTop) (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    (Scheme.Modules.pushforward f).obj (affineDescentAlong f hf M h) ≅ M := by
  let A := specSurjectiveDescent f.appTop hf
    (PiExponent.GlobalSectionClearing.affineToSpecModule M)
    (affineSpecTopSections_annihilator M _ h)
  exact (Scheme.Modules.pushforwardComp Y.isoSpec.inv f).app A ≪≫
    (Scheme.Modules.pushforwardCongr (Scheme.isoSpec_inv_naturality f).symm).app A ≪≫
    ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) X.isoSpec.inv).app A).symm ≪≫
    (Scheme.Modules.pushforward X.isoSpec.inv).mapIso
      (specSurjectiveDescentPushforwardIso f.appTop hf
        (PiExponent.GlobalSectionClearing.affineToSpecModule M)
        (affineSpecTopSections_annihilator M _ h)) ≪≫
    (Scheme.Modules.pushforwardComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
    (Scheme.Modules.pushforwardCongr X.isoSpec.hom_inv_id).app M ≪≫
    (Scheme.Modules.pushforwardId X).app M

theorem exists_affine_closed_descent [IsAffine X] (f : Y ⟶ X) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent]
    (h : RingHom.ker f.appTop.hom ≤ Module.annihilator Γ(X,⊤) Γ(M,⊤)) :
    ∃ N : Y.Modules, Nonempty ((Scheme.Modules.pushforward f).obj N ≅ M) := by
  obtain ⟨hY, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  exact ⟨affineDescentAlong f hf M h, ⟨affineDescentAlongPushforwardIso f hf M h⟩⟩

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPullbackUnitRestriction
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedPullbackUnitRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

lemma restrict_unit_isIso_iff (U : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) ↔
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      (M.restrict U.ι)) := by
  let g := (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
  let e := OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)
  let k := (Scheme.Modules.pushforward (f ∣_ U)).map
    ((OpenBaseChange.leftSquare f U).hom.app M)
  calc
    IsIso g ↔ IsIso (g ≫ e.hom) := (isIso_comp_right_iff g e.hom).symm
    _ ↔ IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        (M.restrict U.ι)) ≫ k) := by rw [OpenBaseChange.unit_compatibility]
    _ ↔ _ := isIso_comp_right_iff _ k

theorem unit_isIso_of_affine (M : X.Modules)
    (h : ∀ U : X.affineOpens,
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U.1)).unit.app
        (M.restrict U.1.ι))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply IdealModule.isIso_of_affine_app
  intro U
  have hr := (restrict_unit_isIso_iff f U.1 M).mpr (h U)
  have ht := Scheme.Modules.Hom.isIso_iff_isIso_app.mp hr ⊤
  change IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app
    (U.1.ι ''ᵁ ⊤)) at ht
  have he : U.1.ι ''ᵁ ⊤ = U.1 :=
    (Scheme.Hom.image_top_eq_opensRange U.1.ι).trans (Scheme.Opens.opensRange_ι U.1)
  rw [he] at ht
  exact ht

end
end PiExponentSeshadri.ClosedPullbackUnitRestriction

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoordinateFrameIdentification
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
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

lemma cocycle_ext {c d : LineBundleGluing.Cocycle U}
    (h : c.transition = d.transition) : c = d := by
  cases c
  cases d
  cases h
  rfl

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalClosedAnnihilatedDescent
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.ClosedAnnihilatedDescent
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

theorem unit_isIso_of_locallyAnnihilated [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply ClosedPullbackUnitRestriction.unit_isIso_of_affine f M
  intro U
  let : IsAffine U.1.toScheme := U.2
  obtain ⟨N, ⟨e⟩⟩ := exists_affine_closed_descent (f ∣_ U.1) (M.restrict U.1.ι) (h U)
  exact ClosedImmersionModules.unit_isIso_of_pushforward (f ∣_ U.1) e.symm

def closedDescentPushforwardIso [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (h : LocallyAnnihilated f M) :
    (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) ≅ M := by
  let := unit_isIso_of_locallyAnnihilated f M h
  exact (asIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).symm

end
end PiExponentSeshadri.ClosedAnnihilatedDescent

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
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

abbrev schemeFreeOpen_p2 (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceResolution
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [AddCommGroup W] [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

theorem coneDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgh : LinearMap.range g = LinearMap.ker h) :
    LinearMap.range (coneDifferential f g r) =
      LinearMap.ker (coneDifferential g h r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨xy, rfl⟩
    exact LinearMap.congr_fun
      (coneDifferential_comp f g h r (comp_zero_of_range_eq_ker f g hfg)
        (comp_zero_of_range_eq_ker g h hgh)) xy
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := congrArg Prod.fst hyz
    have hsecond : h yz.2 = 0 := by
      have hn : -h yz.2 = 0 := congrArg Prod.snd hyz
      exact neg_eq_zero.mp hn
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgh]
      exact hsecond
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

theorem coneBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (π : Z →ₗ[R] Q) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgπ : LinearMap.range g = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (coneDifferential f g r) = LinearMap.ker (coneBottom g r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    have hz : g (f x) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker f g hfg) x
    change g (f x + r • y) + r • (-g y) = 0
    simp [map_add, map_smul, hz]
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := hyz
    have hπg : π (g yz.1) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hgπ) yz.1
    have hrπ : r • π yz.2 = 0 := by
      have heq := congrArg π hfirst
      simpa only [map_add, map_smul, hπg, zero_add, map_zero] using heq
    have hz : π yz.2 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgπ]
      exact hz
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeComplex
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

theorem scalarCone_interior_exact (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (n : ℕ)
    (hnext : LinearMap.range (C.d (n + 3) (n + 2)).hom =
      LinearMap.ker (C.d (n + 2) (n + 1)).hom)
    (hprev : LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom) :
    LinearMap.range (scalarConeMap C r (n + 2)).hom =
      LinearMap.ker (scalarConeMap C r (n + 1)).hom :=
  coneDifferential_exact _ _ _ r hnext hprev

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulFiniteFree
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30

universe u
variable {R : Type u} [CommRing R]

lemma scalarCone_free (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfree 0
  | succ n =>
    let := hfree (n + 1)
    let := hfree n
    change Module.Free R (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_free (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfree n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_free C r hfree)

theorem regularSequenceComplex_free (rs : List R) (n : ℕ) :
    Module.Free R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_free
  intro k
  cases k with
  | zero =>
    change Module.Free R R
    exact Module.Free.self R
  | succ k =>
    change Module.Free R (Fin 0 → R)
    infer_instance

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_KoszulTopTerm
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
variable {R : Type u} [CommRing R]

def scalarConeTopEquiv (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) :
    (W30.scalarConeComplex C r).X (d + 1) ≃ₗ[R] C.X d := by
  letI := hbound (d + 1) (Nat.lt_succ_self d)
  letI : Unique (C.X (d + 1)) :=
    { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  exact LinearEquiv.uniqueProd (R := R) (M := C.X d) (M₂ := C.X (d + 1))

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_KoszulTopDifferential
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open Module
variable {R : Type u} [CommRing R]

def scalarConeTopDualCoordinate (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (e : C.X d ≃ₗ[R] R) :
    Module.Dual R ((W30.scalarConeComplex C r).X (d + 1)) ≃ₗ[R] R :=
  topDualCoordinate ((scalarConeTopEquiv C r d hbound).trans e)

@[simp] theorem scalarConeTopDualCoordinate_apply
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (e : C.X d ≃ₗ[R] R)
    (φ : Module.Dual R ((W30.scalarConeComplex C r).X (d + 1))) :
    scalarConeTopDualCoordinate C r d hbound e φ = φ (0, e.symm 1) := rfl

end PiExponentSiegelAux.W31

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeLocalLength
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]

abbrev ConeAway := Localization.Away (MvPolynomial.X none : ConeRing k σ)
abbrev LaurentChart := LaurentPolynomial (AffineRing k σ)

def coneHomogenizingUnit : (ConeAway k σ)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := ConeAway k σ) (MvPolynomial.X none : ConeRing k σ)).unit

@[simp] theorem coneHomogenizingUnit_val :
    (coneHomogenizingUnit k σ : ConeAway k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) :=
  IsUnit.unit_spec _

@[simp] theorem coneHomogenizingUnit_inv_mul :
    (↑(coneHomogenizingUnit k σ)⁻¹ : ConeAway k σ) *
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X none) = 1 := by
  rw [← coneHomogenizingUnit_val]
  exact Units.inv_mul (coneHomogenizingUnit k σ)

def affineToConeAway : AffineRing k σ →+* ConeAway k σ :=
  MvPolynomial.eval₂Hom
    ((algebraMap (ConeRing k σ) (ConeAway k σ)).comp MvPolynomial.C)
    (fun i => algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
      ↑(coneHomogenizingUnit k σ)⁻¹)

@[simp] theorem affineToConeAway_C (a : k) :
    affineToConeAway k σ (MvPolynomial.C a) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.C a) := by
  simp [affineToConeAway]

@[simp] theorem affineToConeAway_X (i : σ) :
    affineToConeAway k σ (MvPolynomial.X i) =
      algebraMap (ConeRing k σ) (ConeAway k σ) (MvPolynomial.X (some i)) *
        ↑(coneHomogenizingUnit k σ)⁻¹ := by
  simp [affineToConeAway]

def coneToLaurent : ConeRing k σ →+* LaurentChart k σ :=
  MvPolynomial.eval₂Hom (LaurentPolynomial.C.comp MvPolynomial.C)
    (fun i => i.elim (LaurentPolynomial.T 1)
      (fun j => LaurentPolynomial.C (MvPolynomial.X j) * LaurentPolynomial.T 1))

@[simp] theorem coneToLaurent_C (a : k) :
    coneToLaurent k σ (MvPolynomial.C a) =
      LaurentPolynomial.C (MvPolynomial.C a) := by simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_none :
    coneToLaurent k σ (MvPolynomial.X none) = LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

@[simp] theorem coneToLaurent_X_some (i : σ) :
    coneToLaurent k σ (MvPolynomial.X (some i)) =
      LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
  simp [coneToLaurent]

def coneAwayToLaurent : ConeAway k σ →+* LaurentChart k σ :=
  IsLocalization.Away.lift (MvPolynomial.X none : ConeRing k σ)
    (g := coneToLaurent k σ) (by simpa using LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1)

@[simp] theorem coneAwayToLaurent_algebraMap (p : ConeRing k σ) :
    coneAwayToLaurent k σ (algebraMap (ConeRing k σ) (ConeAway k σ) p) =
      coneToLaurent k σ p := by simp [coneAwayToLaurent]

def laurentToConeAway : LaurentChart k σ →+* ConeAway k σ :=
  LaurentPolynomial.eval₂ (affineToConeAway k σ) (coneHomogenizingUnit k σ)

@[simp] theorem laurentToConeAway_C (p : AffineRing k σ) :
    laurentToConeAway k σ (LaurentPolynomial.C p) = affineToConeAway k σ p := by
  simp [laurentToConeAway]

@[simp] theorem laurentToConeAway_T :
    laurentToConeAway k σ (LaurentPolynomial.T 1) = coneHomogenizingUnit k σ := by
  simp [laurentToConeAway]

theorem laurentToConeAway_comp_coneToLaurent :
    (laurentToConeAway k σ).comp (coneToLaurent k σ) =
      algebraMap (ConeRing k σ) (ConeAway k σ) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    cases i with
    | none => simp
    | some i => simp [mul_assoc]

theorem laurentToConeAway_comp_coneAwayToLaurent :
    (laurentToConeAway k σ).comp (coneAwayToLaurent k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
  apply RingHom.ext
  intro p
  change laurentToConeAway k σ
    (coneAwayToLaurent k σ (algebraMap _ _ p)) = algebraMap _ _ p
  rw [coneAwayToLaurent_algebraMap]
  exact RingHom.congr_fun (laurentToConeAway_comp_coneToLaurent k σ) p

theorem coneAwayToLaurent_comp_affineToConeAway :
    (coneAwayToLaurent k σ).comp (affineToConeAway k σ) = LaurentPolynomial.C := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp
  · intro i
    change coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) =
      LaurentPolynomial.C (MvPolynomial.X i)
    apply (LaurentPolynomial.isUnit_T (R := AffineRing k σ) 1).mul_left_inj.mp
    have hu : coneAwayToLaurent k σ (coneHomogenizingUnit k σ) =
        LaurentPolynomial.T 1 := by simp
    calc
      coneAwayToLaurent k σ (affineToConeAway k σ (MvPolynomial.X i)) *
          LaurentPolynomial.T 1 =
          coneAwayToLaurent k σ
            (affineToConeAway k σ (MvPolynomial.X i) * coneHomogenizingUnit k σ) := by
        rw [map_mul, hu]
      _ = LaurentPolynomial.C (MvPolynomial.X i) * LaurentPolynomial.T 1 := by
        simp [mul_assoc]

theorem coneAwayToLaurent_comp_laurentToConeAway :
    (coneAwayToLaurent k σ).comp (laurentToConeAway k σ) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (Polynomial.X : Polynomial (AffineRing k σ)))
  apply Polynomial.ringHom_ext
  · intro a
    change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ (Polynomial.C a))) =
        algebraMap _ _ (Polynomial.C a)
    simp only [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_C,
      laurentToConeAway_C]
    exact RingHom.congr_fun (coneAwayToLaurent_comp_affineToConeAway k σ) a
  · change coneAwayToLaurent k σ
      (laurentToConeAway k σ (algebraMap _ _ Polynomial.X)) =
        algebraMap _ _ Polynomial.X
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]

def coneLaurentEquiv : ConeAway k σ ≃+* LaurentChart k σ :=
  RingEquiv.ofRingHom (coneAwayToLaurent k σ) (laurentToConeAway k σ)
    (coneAwayToLaurent_comp_laurentToConeAway k σ)
    (laurentToConeAway_comp_coneAwayToLaurent k σ)

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConePrimeLocalization
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSiegel.W17.ConeLocalLength

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def awayChartPrime : Ideal (ConeAway k σ) :=
  (laurentPrime (AffineRing k σ) P).comap (coneLaurentEquiv k σ).toRingHom

instance awayChartPrime_isPrime : (awayChartPrime k σ P).IsPrime := by
  unfold awayChartPrime
  infer_instance

def conePrime : Ideal (ConeRing k σ) :=
  (awayChartPrime k σ P).comap (algebraMap (ConeRing k σ) (ConeAway k σ))

instance conePrime_isPrime : (conePrime k σ P).IsPrime := by
  unfold conePrime
  infer_instance

def conePrimeLocalizationEquiv :
    Localization.AtPrime (conePrime k σ P) ≃+*
      Localization.AtPrime (laurentPrime (AffineRing k σ) P) :=
  (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
    (Submonoid.powers (MvPolynomial.X none : ConeRing k σ))
    (awayChartPrime k σ P)).toRingEquiv.trans
      (PiExponentJets.W22.primeLocalizationEquiv (coneLaurentEquiv k σ)
        (awayChartPrime k σ P) (laurentPrime (AffineRing k σ) P) rfl)

def affineLocalToConeLocal : Localization.AtPrime P →+*
    Localization.AtPrime (conePrime k σ P) :=
  (conePrimeLocalizationEquiv k σ P).symm.toRingHom.comp
    (algebraMap (Localization.AtPrime P)
      (Localization.AtPrime (laurentPrime (AffineRing k σ) P)))

@[instance_reducible] def affineLocalConeAlgebra :
    Algebra (Localization.AtPrime P) (Localization.AtPrime (conePrime k σ P)) :=
  (affineLocalToConeLocal k σ P).toAlgebra

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeQuotientAugmentation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
open scoped Pointwise
variable {R Y Z Q : Type*} [CommRing R] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup Q] [Module R Y] [Module R Z] [Module R Q]

theorem coneQuotientAugmentation_exact (g : Y →ₗ[R] Z) (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) (hg : LinearMap.range g = LinearMap.ker π) :
    LinearMap.range (coneBottom g r) = LinearMap.ker (coneQuotientAugmentation π r) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨y, w⟩, rfl⟩
    have hz : π (g y) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hg) y
    change (Submodule.Quotient.mk (π (g y + r • w)) : QuotSMulTop r Q) = 0
    apply (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mpr
    simp only [map_add, map_smul, hz, zero_add]
    exact Submodule.smul_mem_pointwise_smul (π w) r ⊤ (Submodule.mem_top)
  · intro hz
    have hmem : π z ∈ r • (⊤ : Submodule R Q) :=
      (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mp hz
    obtain ⟨q, _, hq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    obtain ⟨w, hw⟩ := hπ q
    have hcycle : π (z - r • w) = 0 := by
      simp only [map_sub, map_smul, hw, hq, sub_self]
    have hrange : z - r • w ∈ LinearMap.range g := by
      rw [hg]
      exact hcycle
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hrange
    refine ⟨(y, w), ?_⟩
    change g y + r • w = z
    rw [hy]
    abel

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ConeRegularSequence
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Localization.AtPrime.algebraOfLiesOver

namespace PiExponentSiegel.W17.ConeLocalLength

open RingTheory.Sequence

variable (k σ : Type*) [CommRing k]
variable (P : Ideal (AffineRing k σ)) [P.IsPrime]

def coneLocalCoordinate : Localization.AtPrime (conePrime k σ P) :=
  algebraMap (ConeRing k σ) (Localization.AtPrime (conePrime k σ P)) (MvPolynomial.X none)

end PiExponentSiegel.W17.ConeLocalLength

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_HomogeneousQuotientDimension
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial
open PiExponentJets.W64
open DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem quotientDegreeProjection_of_mem (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (n m : ℕ) (x : MvPolynomial σ k ⧸ I) (hx : x ∈ quotientSection I m) :
    quotientDegreeProjection I hI n x = if n = m then x else 0 := by
  obtain ⟨p, hp, rfl⟩ := hx
  change quotientDegreeProjection I hI n (Ideal.Quotient.mk I p) = _
  rw [quotientDegreeProjection_mk, GradedAlgebra.proj_apply]
  by_cases hnm : n = m
  · subst n
    rw [DirectSum.decompose_of_mem_same (MvPolynomial.homogeneousSubmodule σ k) hp]
    simp
  · rw [DirectSum.decompose_of_mem_ne (MvPolynomial.homogeneousSubmodule σ k) hp
      (Ne.symm hnm)]
    simp [hnm]

theorem quotientSection_iSupIndep (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    iSupIndep (quotientSection I) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  have hcalc : quotientDegreeProjection I hI i (∑ j ∈ s, v j) = v i := by
    rw [map_sum]
    calc
      ∑ j ∈ s, quotientDegreeProjection I hI i (v j) =
          ∑ j ∈ s, if i = j then v j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact quotientDegreeProjection_of_mem I hI i j (v j) (hv j hj)
      _ = v i := by simp [hi]
  rw [hsum, map_zero] at hcalc
  exact hcalc.symm

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CumulativeHilbertSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentJets.W25

open MvPolynomial DirectSum
open PiExponentJets.W24 PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k]

theorem quotientDegreeFiltration_eq_iSup_sections
    (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    quotientDegreeFiltration I n =
      ⨆ j : Fin (n + 1), quotientSection I j.val := by
  unfold quotientDegreeFiltration quotientSection
  rw [restrictTotalDegree_eq_iSup_homogeneous, Submodule.map_iSup]

theorem cumulativeSectionMap_injective (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    Function.Injective
      (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) :=
  ((quotientSection_iSupIndep I hI).comp Fin.val_injective).dfinsupp_lsum_injective

theorem cumulativeSectionMap_range (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    LinearMap.range
        (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val)) =
      quotientDegreeFiltration I n := by
  rw [DirectSum.range_coeLinearMap, quotientDegreeFiltration_eq_iSup_sections]

def cumulativeHomogeneousQuotientEquiv (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ) :
    (⨁ j : Fin (n + 1), quotientSection I j.val) ≃ₗ[k]
      quotientDegreeFiltration I n :=
  (LinearEquiv.ofInjective
    (DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val))
    (cumulativeSectionMap_injective I hI n)).trans
      (LinearEquiv.ofEq _ _ (cumulativeSectionMap_range I n))

@[simp] theorem cumulativeHomogeneousQuotientEquiv_apply
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ k)) (n : ℕ)
    (x : ⨁ j : Fin (n + 1), quotientSection I j.val) :
    (cumulativeHomogeneousQuotientEquiv I hI n x : MvPolynomial σ k ⧸ I) =
      DirectSum.coeLinearMap (fun j : Fin (n + 1) => quotientSection I j.val) x := rfl

end PiExponentJets.W25

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IteratedKoszulExactness
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSiegelAux.W30
universe u
variable {R : Type u} [CommRing R]

theorem scalarCone_positive_exact (C : ChainComplex (ModuleCat.{u} R) ℕ)
    {Q : Type u} [AddCommGroup Q] [Module R Q] (π : C.X 0 →ₗ[R] Q) (r : R)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hr : IsSMulRegular Q r) (n : ℕ) :
    LinearMap.range ((scalarConeComplex C r).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((scalarConeComplex C r).d (n + 1) n).hom := by
  cases n with
  | zero =>
    change LinearMap.range (coneDifferential (C.d 2 1).hom (C.d 1 0).hom r) =
      LinearMap.ker (coneBottom (C.d 1 0).hom r)
    exact coneBottom_exact (C.d 2 1).hom (C.d 1 0).hom π r (hexact 0) hzero hr
  | succ n =>
    have hd₁ : (scalarConeComplex C r).d (n + 1 + 2) (n + 1 + 1) =
        scalarConeMap C r (n + 1 + 1) := ChainComplex.of_d _ _ (n + 1 + 1)
    have hd₀ : (scalarConeComplex C r).d (n + 1 + 1) (n + 1) =
        scalarConeMap C r (n + 1) := ChainComplex.of_d _ _ (n + 1)
    rw [hd₁, hd₀]
    exact scalarCone_interior_exact C r n (hexact (n + 1)) (hexact n)

theorem iterateScalarCones_exact (rs : List R) {Q : Type u}
    [AddCommGroup Q] [Module R Q] (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (π : C.X 0 →ₗ[R] Q) (hπ : Function.Surjective π)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hreg : RingTheory.Sequence.IsRegular Q rs) :
    ∃ ε : (iterateScalarCones C rs).X 0 →ₗ[R]
        (Q ⧸ (Ideal.ofList rs • ⊤ : Submodule R Q)),
      Function.Surjective ε ∧
      LinearMap.range ((iterateScalarCones C rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((iterateScalarCones C rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((iterateScalarCones C rs).d (n + 1) n).hom := by
  induction rs generalizing Q C with
  | nil =>
    let e := (Ideal.ofList ([] : List R) • (⊤ : Submodule R Q)).quotEquivOfEqBot
      (by simp)
    refine ⟨e.symm.toLinearMap.comp π, e.symm.surjective.comp hπ, ?_, hexact⟩
    calc
      _ = LinearMap.ker π := hzero
      _ = _ := by
        ext x
        change π x = 0 ↔ e.symm (π x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff Q r rs).mp hreg
    let C' := scalarConeComplex C r
    let π' : C'.X 0 →ₗ[R] QuotSMulTop r Q := coneQuotientAugmentation π r
    have hπ' : Function.Surjective π' := coneQuotientAugmentation_surjective π r hπ
    have hz' : LinearMap.range (C'.d 1 0).hom = LinearMap.ker π' := by
      change LinearMap.range (coneBottom (C.d 1 0).hom r) =
        LinearMap.ker (coneQuotientAugmentation π r)
      exact coneQuotientAugmentation_exact (C.d 1 0).hom π r hπ hzero
    have he' : ∀ n, LinearMap.range (C'.d (n + 2) (n + 1)).hom =
        LinearMap.ker (C'.d (n + 1) n).hom :=
      scalarCone_positive_exact C π r hzero hexact hr
    obtain ⟨ε, hε, hzε, heε⟩ := ih C' π' hπ' hz' he' htail
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner Q r rs
    refine ⟨e.symm.toLinearMap.comp ε, e.symm.surjective.comp hε, ?_, heε⟩
    calc
      _ = LinearMap.ker ε := hzε
      _ = _ := by
        ext x
        change ε x = 0 ↔ e.symm (ε x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩

theorem regularSequenceComplex_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ ε : (regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs),
      Function.Surjective ε ∧
      LinearMap.range ((regularSequenceComplex rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((regularSequenceComplex rs).d (n + 1) n).hom := by
  have hzero : LinearMap.range (emptyKoszulComplex.d 1 0).hom =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R) := by
    have hd : (emptyKoszulComplex (R := R)).d 1 0 = 0 :=
      ChainComplex.of_d (emptyKoszulObject (R := R)) (fun _ => 0) 0
    rw [hd]
    change LinearMap.range (0 : (Fin 0 → R) →ₗ[R] R) =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R)
    exact LinearMap.range_zero.trans LinearMap.ker_id.symm
  have hexact : ∀ n : ℕ,
      LinearMap.range ((emptyKoszulComplex (R := R)).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((emptyKoszulComplex (R := R)).d (n + 1) n).hom := by
    intro n
    let : Subsingleton ((emptyKoszulComplex (R := R)).X (n + 1)) := by
      change Subsingleton (Fin 0 → R)
      infer_instance
    exact Subsingleton.elim _ _
  have h := iterateScalarCones_exact rs emptyKoszulComplex
    (LinearMap.id : R →ₗ[R] R) Function.surjective_id hzero hexact hreg
  have hI : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    exact Ideal.mul_top _
  rw [hI] at h
  exact h

end PiExponentSiegelAux.W30

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalIntersectionTransport
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

noncomputable def scalarKernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)) ≃ₗ[A]
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) :=
  e.ofSubmodules _ _ (map_scalar_kernel e x)

end PiExponentJets.W28.LocalIntersection

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_LocalizationQuotientParameters
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

variable {A : Type*} [CommRing A]

instance quotientParameterPrime_isMaximal (I m : Ideal A) [m.IsMaximal] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk I) (m := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

end PiExponentSiegel.W23

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_NaturalMultiplicityPropagation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def parentChildIncidenceEquiv
    (I T : Ideal (MvPolynomial σ k)) (x : MvPolynomial σ k) :
    (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T, MinimalParentsBelow I Q.val) ≃
      (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}) where
  toFun z := ⟨⟨z.2.val, z.2.property.1, z.2.property.2.trans z.1.property.2⟩,
    z.1, z.2.property.2⟩
  invFun z := ⟨z.2.val, z.1.val, z.1.property.1, z.2.property⟩
  left_inv := by rintro ⟨Q,P⟩; rfl
  right_inv := by rintro ⟨P,Q⟩; rfl

end PiExponentJets.W22

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_RegularSequenceExt
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

def regularSequenceAugmentation (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (W30.regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs) :=
  (W30.regularSequenceComplex_exact rs hreg).choose

theorem regularSequenceAugmentation_spec (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    Function.Surjective (regularSequenceAugmentation rs hreg) ∧
    LinearMap.range ((W30.regularSequenceComplex rs).d 1 0).hom =
      LinearMap.ker (regularSequenceAugmentation rs hreg) ∧
    ∀ n, LinearMap.range ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((W30.regularSequenceComplex rs).d (n + 1) n).hom :=
  (W30.regularSequenceComplex_exact rs hreg).choose_spec

def regularSequenceResolution (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  moduleFreeResolutionOfExact (W30.regularSequenceComplex rs)
    (ModuleCat.of R (R ⧸ Ideal.ofList rs))
    (ModuleCat.ofHom (regularSequenceAugmentation rs hreg))
    (by
      apply ModuleCat.hom_ext
      exact LinearMap.range_le_ker_iff.mp (regularSequenceAugmentation_spec rs hreg).2.1.le)
    (regularSequenceAugmentation_spec rs hreg).2.1
    (regularSequenceAugmentation_spec rs hreg).1
    (regularSequenceAugmentation_spec rs hreg).2.2
    (W30.regularSequenceComplex_free rs)

end PiExponentSiegelAux.W31

end

end OAI
end


