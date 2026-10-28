-- Prove2me | Definitions.Def_OAIQ068A030
-- name    : OAIQ068A030
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T08:03:01.566503+00:00
-- url     : https://prove2.me/theorems/347d4b0b-e87b-4f28-a174-044dc83a28d4
-- title:
--   Definitions bundle OAIQ068A030 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 95 declarations of OpenAI's Lean: 26 definitions, 1 inductive type or structure, 4 instances and 64 theorems. The definitions and types are `OAI.PiExponent.ClosedImmersionSerreTransfer.cohomologyLinearMap`, `OAI.PiExponent.ClosedImmersionSerreTransfer.typedCohomologyMap`, `OAI.PiExponent.CoherentExtFiniteness.CoherentFinitePresentation`, `OAI.PiExponent.CurveNormalizationDegree.unitMap`, `OAI.PiExponent.GeometrySupport.CechLinear.primitive`, `OAI.PiExponent.GeometrySupport.CechZero.augmentationLinear`, `OAI.PiExponent.GeometrySupport.CechZero.schemeFreeOpen`, `OAI.PiExponent.GeometrySupport.FreeCechSections.sectionValuesEquiv`, `OAI.PiExponent.GeometrySupport.FreeCechSections.sectionsEquiv`, `OAI.PiExponent.GeometrySupport.FreeCechSections.tupleNatEquiv`, `OAI.PiExponent.GeometrySupport.TwistPresentations.presentationKernel`, `OAI.PiExponent.GeometrySupport.TwistPresentations.twistFreeIsoBiproduct`, `OAI.PiExponent.GlobalSectionClearing.overlapDifference`, `OAI.PiExponent.NegativeTwistPresentations.cancelIso`, `OAI.PiExponent.NegativeTwistPresentations.middleIsoBiproduct`, `OAI.PiExponent.NegativeTwistPresentations.presentationMap`, `OAI.PiExponent.ProjectivePencil.coordinateSection`, `OAI.PiExponent.ProjectivePencil.lineBundle`, `OAI.PiExponentSeshadri.Geometry.BaseSections.cohomologyZero`, `OAI.PiExponentSeshadri.Geometry.BaseSections.globalIntersection`, `OAI.PiExponentSeshadri.Geometry.BaseSections.globalSectionsLinear`, `OAI.PiExponentSeshadri.Geometry.lineTensorPresheafRestrictFrame`, `OAI.PiExponentSeshadri.Geometry.moduleLineTensorAssoc`, `OAI.PiExponentSeshadri.Geometry.moduleTwistPowerIso`, `OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeftLinePair`, `OAI.PiExponentSeshadri.Projective.coordinateFramedOverlap`, `OAI.PiExponentSeshadri.Projective.coordinateFramedTuple`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AmpleGlobalGeneration`, `PiExponent_Approximation_ClosedPushforwardLinear`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_ModuleLinePowerLaws`, `PiExponent_Approximation_NegativeTwistPresentations`, `PiExponent_Approximation_TensorPure`, `PiExponent_Approximation_TwistGlobalExtension`, `PiExponent_Approximation_TwistPresentations`, `PiExponent_Approximation_TwistSectionClearing`, `PiExponent_Approximation_TwistSectionScalars`, `PiExponent_Cohomology_CechHigher`, `PiExponent_Cohomology_CechLinear`, `PiExponent_Cohomology_CechOne`, `PiExponent_Cohomology_CechZero`, `PiExponent_Cohomology_FreeCechSections`, `PiExponent_Cohomology_PencilCohomology`, `PiExponent_Cohomology_PencilCohomologyFiniteCharts`, `PiExponent_Cohomology_ProjectiveFramedCech`, `PiExponent_Geometry_CurveNormalizationNonaffine`, `PiExponent_Geometry_CurveNormalizationUnit`, `PiExponent_Geometry_ProjectiveFinitePencil`, `PiExponent_Geometry_ProjectiveSectionsPullback`, `PiExponent_Geometry_SheafSectionGluing`, `PiExponent_LocalAlgebra_CoherentExtFiniteness`, `PiExponent_LocalAlgebra_FiniteGlobalPresentation`.
--
--   **Imports.** It imports the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022` and `OAIQ068A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A036`, `OAIQ068A037`, `OAIQ068A038` and `OAIQ068A039`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Definitions.Def_OAIQ068A020
import Definitions.Def_OAIQ068A021
import Definitions.Def_OAIQ068A022
import Definitions.Def_OAIQ068A023

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

theorem moduleTensorMap_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (L : LineBundle X) : Epi (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Epi (F.map f) := inferInstanceAs
    (Epi ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Epi (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

theorem moduleTensorMap_mono {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (L : LineBundle X) : Mono (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Mono (F.map f) := inferInstanceAs
    (Mono ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Mono (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

instance moduleTensorRightFunctor_additive (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).Additive where
  map_add {M N} {f g} := by
    apply sub_eq_zero.mp
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let F := Scheme.Modules.restrictFunctor U.ι
    let T := moduleTensorRightFunctor L.sheaf
    let E := moduleTensorRestrictFrame U L.sheaf e
    have h (a : M ⟶ N) : F.map (T.map a) =
        (E.app M).hom ≫ F.map a ≫ (E.app N).inv := by
      apply (cancel_mono (E.app N).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact E.hom.naturality a
    change F.map (T.map (f + g) - (T.map f + T.map g)) = 0
    rw [F.map_sub, F.map_add, h (f+g), h f, h g, F.map_add,
      Preadditive.add_comp, Preadditive.comp_add, sub_self]

instance moduleTwistFunctor_additive (L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor L n).Additive := by
  induction n with
  | zero => change (𝟭 X.Modules).Additive; infer_instance
  | succ n ih =>
    change (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf).Additive
    infer_instance

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

lemma restrictedOpenSections_naturality (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : Y.Opens} (h : U ≤ V) (m : OpenSections (M.restrict f) V) :
    restrictedOpenSections M f U (openRestriction (M.restrict f) h m) =
      openRestriction M (f.image_mono h) (restrictedOpenSections M f V m) := rfl

theorem affine_basicOpen_zero [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := affine_openRestriction_localize M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r)
      (openRestriction M (X.basicOpen_le r))).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

lemma openRestriction_comp_apply (M : X.Modules) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (x : OpenSections M W) :
    openRestriction M hUV (openRestriction M hVW x) =
      openRestriction M (hUV.trans hVW) x := by
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  erw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

lemma affine_immersion_zero_on [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (r : Γ(X,⊤))
    (U : X.Opens) (hU : f ''ᵁ (⊤ : Y.Opens) ≤ U) (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M hU (r ^ n • x) = 0 := by
  let x' := (restrictedOpenSections M f ⊤).symm
    (openRestriction M hU x)
  have hWD : f ''ᵁ (Y.basicOpen (f.appTop r)) ≤ U ⊓ X.basicOpen r := by
    apply le_inf
    · exact (f.image_mono le_top).trans hU
    · rw [← Scheme.preimage_basicOpen_top]
      exact f.image_preimage_le _
  have hx' : openRestriction (M.restrict f) (Y.basicOpen_le (f.appTop r)) x' = 0 := by
    apply (restrictedOpenSections M f _).injective
    rw [map_zero, restrictedOpenSections_naturality]
    simp only [x', LinearEquiv.apply_symm_apply]
    rw [openRestriction_comp_apply]
    rw [← openRestriction_comp_apply M hWD (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x, hx, map_zero]
  obtain ⟨N, hN⟩ := affine_basicOpen_zero (M.restrict f) (f.appTop r) x' hx'
  refine ⟨N, fun n hn => ?_⟩
  have hi := congrArg (restrictedOpenSections M f ⊤) (hN n hn)
  let : Module Γ(X,⊤) (OpenSections (M.restrict f) ⊤) :=
    Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have hscalar : (f.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (f.appTop r) ^ n • x' = f.appTop (r ^ n) • x'
    rw [map_pow]
  rw [hscalar, map_smul, map_zero] at hi
  simpa only [x', LinearEquiv.apply_symm_apply, map_smul] using hi

lemma openSectionsCongr_naturality (M : X.Modules) {U V U' V' : X.Opens}
    (eU : U = U') (eV : V = V') (h : U ≤ V) (h' : U' ≤ V')
    (x : OpenSections M V) :
    openSectionsCongr M eU (openRestriction M h x) =
      openRestriction M h' (openSectionsCongr M eV x) := by
  subst U' V'
  rfl

lemma affineOpenPrincipalEquiv_restrict (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens)
    (y : OpenSections (M.restrict U.ι) ⊤) :
    affineOpenPrincipalEquiv M r U
      (openRestriction (M.restrict U.ι) (U.toScheme.basicOpen_le (U.ι.appTop r)) y) =
    openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left)
      (affineOpenTopEquiv M U y) := by
  dsimp only [affineOpenPrincipalEquiv, affineOpenTopEquiv, LinearEquiv.trans_apply]
  rw [restrictedOpenSections_naturality]
  exact openSectionsCongr_naturality M (principal_open_image r U) U.ι_image_top _ _ _

theorem affine_open_section_extends (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsAffineOpen U)
    (x : OpenSections M (U ⊓ X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M U,
      openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y = r ^ n • x := by
  let : IsAffine U.toScheme := hU
  let : Module Γ(X,⊤) (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) :=
    Module.compHom _ U.ι.appTop.hom
  let x' := (affineOpenPrincipalEquiv M r U).symm x
  obtain ⟨n, y, hy⟩ := affine_basicOpen_denominators (M.restrict U.ι) (U.ι.appTop r) x'
  refine ⟨n, affineOpenTopEquiv M U y, ?_⟩
  have hscalar : (U.ι.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (U.ι.appTop r) ^ n • x' = U.ι.appTop (r ^ n) • x'
    rw [map_pow]
  have hh := congrArg (affineOpenPrincipalEquiv M r U) hy
  rw [hscalar, map_smul, affineOpenPrincipalEquiv_restrict] at hh
  simpa only [x', LinearEquiv.apply_symm_apply] using hh

def overlapDifference (M : X.Modules) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V) : OpenSections M (U ⊓ V) :=
  openRestriction M inf_le_left y - openRestriction M inf_le_right z

lemma overlapDifference_restrict_zero (M : X.Modules) (r : Γ(X,⊤))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V)
    (hy : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y =
      r ^ N • openRestriction M inf_le_right x)
    (hz : openRestriction M (show V ⊓ X.basicOpen r ≤ V from inf_le_left) z =
      r ^ N • openRestriction M inf_le_right x) :
    openRestriction M (show (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ V from inf_le_left)
      (overlapDifference M y z) = 0 := by
  have hU : (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ X.basicOpen r := inf_le_inf inf_le_left le_rfl
  have hV : (U ⊓ V) ⊓ X.basicOpen r ≤ V ⊓ X.basicOpen r := inf_le_inf inf_le_right le_rfl
  calc
    _ = openRestriction M hU (openRestriction M inf_le_left y) -
        openRestriction M hV (openRestriction M inf_le_left z) := by
      simp only [overlapDifference, map_sub, openRestriction_comp_apply]
    _ = 0 := by
      rw [hy, hz, map_smul, map_smul, openRestriction_comp_apply, openRestriction_comp_apply,
        sub_self]

lemma overlapDifference_smul_zero_iff (M : X.Modules) (r : Γ(X,⊤))
    {U V : X.Opens} (y : OpenSections M U) (z : OpenSections M V) (K : ℕ) :
    r ^ K • overlapDifference M y z = 0 ↔
      openRestriction M (show U ⊓ V ≤ U from inf_le_left) (r ^ K • y) =
      openRestriction M (show U ⊓ V ≤ V from inf_le_right) (r ^ K • z) := by
  simp only [overlapDifference, smul_sub, map_smul, sub_eq_zero]

lemma restriction_of_glued_power (M : X.Modules) (r : Γ(X,⊤))
    {ι : Type*} (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (X.basicOpen r)) (N K : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x)
    (z : OpenSections M ⊤)
    (hz : ∀ i, openRestriction M (show U i ≤ ⊤ from le_top) z = r ^ K • y i) :
    openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => U i ⊓ X.basicOpen r)
    (X.basicOpen r) (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction M inf_le_right (openRestriction M (X.basicOpen_le r) z) =
    openRestriction M inf_le_right (r ^ (N + K) • x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) le_top z,
    hz i, map_smul, hy i, map_smul, ← mul_smul, ← pow_add, Nat.add_comm K N]

theorem finite_affine_local_extensions (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections M (U i),
      ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
        r ^ N • openRestriction M inf_le_right x := by
  classical
  choose n y hy using fun i => affine_open_section_extends M r (U i) (hU i)
    (openRestriction M (show U i ⊓ X.basicOpen r ≤ X.basicOpen r from inf_le_right) x)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => r ^ (N - n i) • y i, fun i => ?_⟩
  rw [map_smul, hy i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i))]

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorPure
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

attribute [local instance] OAI.PiExponentSeshadri.TensorPure.sectionModule
lemma right_unit_pure (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (a : Γ(X,U)) :
    (moduleTensorRightUnit M).hom.app U (pure M (structureSheaf X) U m a) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (ρ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorRightUnit M).hom = (ρ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] a)) h

end PiExponentSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSectionScalars
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme}

lemma moduleSectionMultiplyRight_pure (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens) (m : Γ(M,U)) :
    (moduleSectionMultiplyRight M s).app U m =
      pure M L U m (s.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorRightUnit M).hom.app U
      (pure M (structureSheaf X) U m (1 : Γ(X,U))) = m := by
    erw [right_unit_pure, one_smul]
  have hi : (moduleTensorRightUnit M).inv.app U m =
      pure M (structureSheaf X) U m (1 : Γ(X,U)) := by
    calc
      _ = (moduleTensorRightUnit M).inv.app U
          ((moduleTensorRightUnit M).hom.app U
            (pure M (structureSheaf X) U m (1 : Γ(X,U)))) := congrArg _ h.symm
      _ = _ := congrArg (fun q => q.app U
        (pure M (structureSheaf X) U m (1 : Γ(X,U)))) (moduleTensorRightUnit M).hom_inv_id
  change (moduleTensorMap (𝟙 M) s).app U ((moduleTensorRightUnit M).inv.app U m) = _
  erw [hi, TensorPure.map_pure]
  rfl

lemma moduleTensorFrame_pure (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) (U : X.Opens) (m : Γ(M,U)) (l : Γ(L,U)) :
    (moduleTensorFrame M e).hom.app U (pure M L U m l) =
      (show Γ(X,U) from e.hom.app U l) • m := by
  change (moduleTensorRightUnit M).hom.app U
    ((moduleTensorMap (𝟙 M) e.hom).app U (pure M L U m l)) = _
  have h := TensorPure.map_pure (𝟙 M) e.hom U m l
  exact (congrArg (fun t => (moduleTensorRightUnit M).hom.app U t) h).trans
    (right_unit_pure M U m (e.hom.app U l))

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSectionClearing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TwistSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing
variable {X : Scheme}

lemma frame_local_input_zero_on (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (P : X.Modules) (W : X.Opens) (V : U.toScheme.Opens) (hVW : U.ι ''ᵁ V ≤ W)
    (x : Γ(P,W))
    (hx : P.presheaf.map (homOfLE
      (show W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s ≤ W from inf_le_left)).op x = 0) :
    (P.restrict U.ι).presheaf.map (homOfLE
      (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left)).op
      (P.presheaf.map (homOfLE hVW).op x) = 0 := by
  have hD : U.ι ''ᵁ (V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s))) ≤
      W ⊓ PiExponentSeshadri.SectionOpens.isoOpen s := by
    apply le_inf
    · exact (U.ι.image_mono inf_le_left).trans hVW
    · apply (U.ι.image_mono inf_le_right).trans
      rw [← preimage_isoOpen s U.ι e]
      exact U.ι.image_preimage_le _
  change _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P (U.ι.image_mono
    (show V ⊓ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) ≤ V from inf_le_left))
    (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P hVW x) = 0
  erw [openRestriction_comp_apply]
  erw [← openRestriction_comp_apply P hD inf_le_left x]
  change _root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P hD (P.presheaf.map (homOfLE inf_le_left).op x) = 0
  rw [hx]
  exact map_zero (_root_.OAI.PiExponent.GlobalSectionClearing.openRestriction P hD)

end
end PiExponent.TwistSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_SheafSectionGluing
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.SheafSectionGluing
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponent.GlobalSectionClearing
universe u
variable {X : Scheme.{u}} {P Q : X.Modules}

lemma mapSection_naturality (f : P ⟶ Q) {U V : X.Opens} (h : U ≤ V)
    (x : OpenSections P V) :
    mapSection f U (openRestriction P h x) = openRestriction Q h (mapSection f V x) :=
  CategoryTheory.congr_fun (f.mapPresheaf.naturality (homOfLE h).op) x

theorem glue_after_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i j,
      mapSection f (U i ⊓ U j) (openRestriction P inf_le_left (y i)) =
        mapSection f (U i ⊓ U j) (openRestriction P inf_le_right (y j))) :
    ∃ z : OpenSections Q ⊤,
      ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i) := by
  have h := TopCat.Sheaf.existsUnique_gluing' ⟨_, Q.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover])
    (fun i => mapSection f (U i) (y i)) ?_
  · obtain ⟨z, hz, _⟩ := h
    exact ⟨z, hz⟩
  · intro i j
    change openRestriction Q (show U i ⊓ U j ≤ U i from inf_le_left) (mapSection f (U i) (y i)) =
      openRestriction Q (show U i ⊓ U j ≤ U j from inf_le_right) (mapSection f (U j) (y j))
    rw [← mapSection_naturality, ← mapSection_naturality]
    exact hy i j

theorem restriction_of_glued_map (f : P ⟶ Q) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (D : X.Opens) (x : OpenSections P D)
    (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x)
    (z : OpenSections Q ⊤)
    (hz : ∀ i, openRestriction Q (show U i ≤ ⊤ from le_top) z = mapSection f (U i) (y i)) :
    openRestriction Q (show D ≤ ⊤ from le_top) z = mapSection f D x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, Q.isSheaf⟩ (fun i => U i ⊓ D) D
    (fun i => homOfLE inf_le_right) (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction Q inf_le_right (openRestriction Q (show D ≤ ⊤ from le_top) z) =
    openRestriction Q inf_le_right (mapSection f D x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply Q (show U i ⊓ D ≤ U i from inf_le_left) le_top z,
    hz i, ← mapSection_naturality, hy i, mapSection_naturality]

theorem overlap_difference_zero {ι : Type*} (U : ι → X.Opens) (D : X.Opens)
    (x : OpenSections P D) (y : ∀ i, OpenSections P (U i))
    (hy : ∀ i, openRestriction P (show U i ⊓ D ≤ U i from inf_le_left) (y i) =
      openRestriction P inf_le_right x) (i j : ι) :
    openRestriction P (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ U j from inf_le_left)
      (openRestriction P inf_le_left (y i) - openRestriction P inf_le_right (y j)) = 0 := by
  rw [map_sub, openRestriction_comp_apply, openRestriction_comp_apply]
  have hi := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U i ⊓ D from inf_le_inf inf_le_left le_rfl)) (hy i)
  have hj := congrArg (openRestriction P
    (show (U i ⊓ U j) ⊓ D ≤ U j ⊓ D from inf_le_inf inf_le_right le_rfl)) (hy j)
  simp only [openRestriction_comp_apply] at hi hj
  rw [hi, hj, sub_self]

end
end PiExponent.SheafSectionGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistGlobalExtension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.TwistGlobalExtension
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GlobalSectionClearing PiExponent.SheafSectionGluing
variable {X : Scheme}

lemma section_open_image {L : X.Modules} (s : structureSheaf X ⟶ L)
    (U : X.Opens) (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
      U ⊓ sectionOpen X s := by
  change U.ι ''ᵁ U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) =
    U ⊓ PiExponentSeshadri.SectionOpens.isoOpen s
  rw [← preimage_isoOpen s U.ι e, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]
  rfl

lemma mapSection_twistSection_add (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf)
    (M : X.Modules) (D : X.Opens) (x : _root_.OAI.PiExponent.GlobalSectionClearing.OpenSections M D) (n k : ℕ) :
    mapSection ((moduleTwistForward L s n k).app M) D
      (mapSection ((moduleTwistSection L s n).app M) D x) =
    mapSection ((moduleTwistSection L s (n+k)).app M) D x := by
  exact congrArg (fun t => mapSection (t.app M) D x) (moduleTwistSection_add L s n k).symm

end
end PiExponent.TwistGlobalExtension

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_FiniteGlobalPresentation
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

theorem moduleTwist_isFinitePresentation {X : Scheme.{0}}
    (L : PiExponentSeshadri.Geometry.LineBundle X) (n : ℕ) (M : X.Modules)
    [M.IsFinitePresentation] :
    ((PiExponentSeshadri.Geometry.moduleTwistFunctor L n).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_locally_iso M
  intro x
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U,hxU,⟨(PiExponentSeshadri.Geometry.moduleTwistRestrictFrame L U e n).app M⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleGlobalGeneration
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.AmpleGlobalGeneration
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CoherentAffineFinite
variable {X : Scheme.{0}}

theorem sectionMultiply_isIso_restrict (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (moduleSectionMultiplyRight M s)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap (𝟙 M) s)) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U M L).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s))
  rw [Functor.map_comp]
  infer_instance

theorem twistSection_isIso_restrict (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (M : X.Modules) (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      ((moduleTwistSection L s n).app M)) := by
  have : IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map s) :=
    PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  induction n with
  | zero => change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map (𝟙 M)); infer_instance
  | succ n ih =>
    change IsIso ((Scheme.Modules.restrictFunctor (sectionOpen X s).ι).map
      (((moduleTwistSection L s n).app M) ≫
        moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s))
    rw [Functor.map_comp]
    have := sectionMultiply_isIso_restrict ((moduleTwistFunctor L n).obj M) s (sectionOpen X s)
    infer_instance

lemma openSectionEquiv_postcomp {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (a : structureSheaf U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv N U (a ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
      f.app U (openSectionEquiv M U a) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op
    (f.app (U.ι ''ᵁ ⊤) (a.app ⊤ (1 : Γ(U.toScheme,⊤)))) =
    f.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op
      (a.app ⊤ (1 : Γ(U.toScheme,⊤))))
  exact (congr($(f.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (a.app ⊤ (1 : Γ(U.toScheme,⊤))))).symm

end
end PiExponent.AmpleGlobalGeneration

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ClosedPushforwardLinear
attribute [-instance] _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
local instance closedPushforwardLinearSourceHasExt_r997952_1 : HasExt.{1} X.Modules := schemeHasExt
local instance closedPushforwardLinearTargetHasExt : HasExt.{1} Y.Modules := schemeHasExt

variable [IsClosedImmersion f]

lemma cohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    cohomologyMap f N k (x.comp y h) =
      (cohomologyMap f M n x).comp (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom_comp
    (Scheme.Modules.pushforward f) (structureMap f) x y h

def typedCohomologyMap (M : X.Modules) (n : ℕ) :
    cohomology M n →+ cohomology ((Scheme.Modules.pushforward f).obj M) n :=
  cohomologyMap f M n

lemma typedCohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    typedCohomologyMap f N k (x.comp y h) =
      (typedCohomologyMap f M n x).comp
        (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  cohomologyMap_comp f x y h

def cohomologyLinearMap (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact { toFun := typedCohomologyMap f M n
          map_add' := (typedCohomologyMap f M n).map_add
          map_smul' := by
            intro r x
            change typedCohomologyMap f M n ((baseScalars (f ≫ p) r) • x) =
              (baseScalars p r) • (typedCohomologyMap f M n x)
            rw [Ext.smul_eq_comp_mk₀, typedCohomologyMap_comp, Ext.smul_eq_comp_mk₀,
              Ext.mapExactFunctor_mk₀]
            congr 2
            ext U m
            change Γ(M, f ⁻¹ᵁ U) at m
            change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • m =
              f.app U (restrictScalar Y U (baseScalars p r)) • m
            rw [scalar_naturality] }

lemma cohomologyLinearMap_eq (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    ⇑(cohomologyLinearMap f p M n) = typedCohomologyMap f M n := rfl

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_ModuleLinePowerLaws
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open PiExponentSeshadri.TensorPure
variable {X : Scheme}

def lineTensorPresheafRestrictFrame (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    (modulePresheafRestrict U.ι).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val) ≅
        (N.restrict U.ι).val := by
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.presheaf)
  let ep : (modulePresheafRestrict U.ι).obj L.sheaf.val ≅
      𝟙_ (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    (SheafOfModules.forget _).mapIso e
  exact modulePresheafTensorRestrict U L.sheaf.val N.val ≪≫
    tensorIso ep (Iso.refl _) ≪≫ λ_ _

lemma lineTensorPresheaf_unit_restrict_isIso (L : LineBundle X) (N : X.Modules)
    (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    IsIso ((modulePresheafRestrict U.ι).map
      ((adj X).unit.app
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val))) := by
  let P := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  have hη : IsIso ((adj U.toScheme).unit.app (R.obj P)) :=
    sheafification_unit_isIso_of_iso (R.obj P) (N.restrict U.ι)
      (lineTensorPresheafRestrictFrame L N U e)
  have hh : IsIso (R.map ((adj X).unit.app P) ≫
      ((moduleSheafificationRestrict U.ι).hom.app P).val) := by
    erw [sheafify_restrict_unit]
    exact hη
  let V : U.toScheme.Modules ⥤ PresheafOfModules U.toScheme.ringCatSheaf.obj :=
    SheafOfModules.forget U.toScheme.ringCatSheaf
  let hv : IsIso (C := PresheafOfModules U.toScheme.ringCatSheaf.obj)
      (((moduleSheafificationRestrict U.ι).hom.app P).val) :=
    (V.mapIso ((moduleSheafificationRestrict U.ι).app P)).isIso_hom
  exact (@isIso_comp_right_iff (PresheafOfModules U.toScheme.ringCatSheaf.obj)
    _ _ _ _ _ _ hv).mp hh

lemma sheafification_tensor_left_line_unit_isIso (M : X.Modules) (L : LineBundle X)
    (N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val)
        ((adj X).unit.app
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val)))) := by
  let P := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.val
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let Q := (F ⋙ SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  let g := PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 M.val) η
  apply PiExponent.NumericalAmpleness.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U,hx,?_⟩
  let R : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.presheaf)
  have : IsIso (R.map η) := lineTensorPresheaf_unit_restrict_isIso L N U e
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict U.ι) g).mpr
  change IsIso (S.map (R.map g))
  have heq := modulePresheafTensorRestrict_natural U (𝟙 M.val) η
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val P).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val P)).isIso_hom
  let : IsIso (S.map (modulePresheafTensorRestrict U M.val Q).hom) :=
    (S.mapIso (modulePresheafTensorRestrict U M.val Q)).isIso_hom
  have hcomp : IsIso (S.map (R.map g ≫
      (modulePresheafTensorRestrict U M.val Q).hom)) := by
    erw [heq, S.map_comp]
    have ht : IsIso (S.map
      (PresheafOfModules.Monoidal.tensorHom (R := U.toScheme.presheaf)
        (R.map (𝟙 M.val)) (R.map η))) := by
      rw [R.map_id]
      change IsIso (S.map ((𝟙 (R.obj M.val)) ⊗ₘ (R.map η)))
      infer_instance
    exact (inferInstance : IsIso (C := U.toScheme.Modules)
      (S.map (modulePresheafTensorRestrict U M.val P).hom ≫ S.map
        (PresheafOfModules.Monoidal.tensorHom (R := U.toScheme.presheaf)
          (R.map (𝟙 M.val)) (R.map η))))
  erw [S.map_comp] at hcomp
  exact (isIso_comp_right_iff (C := U.toScheme.Modules) _ _).mp hcomp

def sheafificationTensorLeftLinePair (M : X.Modules) (L N : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val)) ≅
    moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let P := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val N.sheaf.val
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (adj X).unit.app P
  let ht : IsIso (F.map (PresheafOfModules.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 M.val) η)) := sheafification_tensor_left_line_unit_isIso M L N.sheaf
  exact @asIso _ _ _ _ (F.map (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 M.val) η)) ht

def moduleLineTensorAssoc (M : X.Modules) (L N : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅
      moduleTensor X M (moduleTensor X L.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (M.val ⊗ L.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ M.val L.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeftLinePair M L N

def moduleTwistPowerIso (L : LineBundle X) (M : X.Modules) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj M ≅ moduleTensor X M (modulePow X L.sheaf n)
  | 0 => (moduleTensorRightUnit M).symm
  | n+1 => moduleTensorIso (moduleTwistPowerIso L M n) (Iso.refl L.sheaf) ≪≫
      moduleLineTensorAssoc M (L.pow n) L ≪≫
      moduleTensorIso (Iso.refl M) (moduleTensorComm (modulePow X L.sheaf n) L.sheaf)

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistPresentations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def twistFreeIsoBiproduct [HasFiniteBiproducts X.Modules]
    (L : LineBundle X) (n : ℕ) (I : Type) [Fintype I] :
    (moduleTwistFunctor L n).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ⨁ (fun _ : I => modulePow X L.sheaf n) :=
  (moduleTwistFunctor L n).mapIso
      (biproduct.isoCoproduct (fun _ : I => structureSheaf X)).symm ≪≫
    (moduleTwistFunctor L n).mapBiproduct (fun _ : I => structureSheaf X) ≪≫
    biproduct.mapIso (fun _ : I => moduleTwistUnitIso L n)

variable (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections)

abbrev presentationKernel : X.Modules := kernel (C := X.Modules) s.π

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_CoherentExtFiniteness
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

structure CoherentFinitePresentation (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) where
  kernel : X.Modules
  kernel_coherent : kernel.IsFinitePresentation
  middle : X.Modules
  left : kernel ⟶ middle
  right : middle ⟶ M
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  middle_finite : ∀ q, letI := Module.compHom (cohomology middle q) (baseScalars p)
    FiniteDimensional ℂ (cohomology middle q)

end
end PiExponent.CoherentExtFiniteness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_NegativeTwistPresentations
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NegativeTwistPresentations
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport.TwistPresentations
variable {X : Scheme.{0}}

def cancelIso (M : X.Modules) (L N : LineBundle X)
    (e : moduleTensor X L.sheaf N.sheaf ≅ structureSheaf X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅ M :=
  moduleLineTensorAssoc M L N ≪≫ moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

variable (L N : LineBundle X) {M : X.Modules} {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections)
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)

def presentationMap : moduleTensor X (SheafOfModules.free s.I) N.sheaf ⟶ M :=
  moduleTensorMap (s.π ≫ (moduleTwistPowerIso L M n).hom) (𝟙 N.sheaf) ≫
    (cancelIso M (L.pow n) N e).hom

instance presentationMap_epi : Epi (presentationMap L N s e) := by
  let g : (SheafOfModules.free s.I : X.Modules) ⟶ moduleTensor X M (L.pow n).sheaf :=
    s.π ≫ (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) s.π := s.epi
  let hg : Epi (C := X.Modules) g := epi_comp (C := X.Modules) s.π (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf)) :=
    @moduleTensorMap_epi X _ _ g hg N
  exact epi_comp (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf))
    (cancelIso M (L.pow n) N e).hom

def middleIsoBiproduct [Fintype s.I] [HasFiniteBiproducts X.Modules] :
    moduleTensor X (SheafOfModules.free s.I) N.sheaf ≅ ⨁ (fun _ : s.I => N.sheaf) :=
  twistFreeIsoBiproduct N 1 s.I ≪≫
    biproduct.mapIso (fun _ : s.I => moduleTensorRightUnit N.sheaf)

theorem middle_isFinitePresentation [hs : s.IsFiniteType] :
    (moduleTensor X (SheafOfModules.free s.I) N.sheaf).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X s.I
  exact PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation N 1
    (SheafOfModules.free s.I)

theorem kernel_isFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    [s.IsFiniteType] : (kernel (presentationMap L N s e)).IsFinitePresentation := by
  have := middle_isFinitePresentation L N s
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation (presentationMap L N s e)

theorem presentation_shortExact :
    (ShortComplex.mk (kernel.ι (presentationMap L N s e)) (presentationMap L N s e)
      (kernel.condition (presentationMap L N s e))).ShortExact :=
  { exact := ShortComplex.exact_kernel (presentationMap L N s e) }

end
end PiExponent.NegativeTwistPresentations

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechOne
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

theorem hom_glue {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f : ∀ i, freeOpen R (U i) ⟶ M)
    (hf : ∀ i j, freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) ≫ f i =
      freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)) ≫ f j) :
    ∃ g : freeOpen R V ⟶ M, ∀ i, freeOpenMap R (homOfLE (hUV i)) ≫ g = f i := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  let sf (i : J) := freeOpenEquiv R M (U i) (f i)
  have hc : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    change M.val.map (homOfLE inf_le_left).op (sf i) =
      M.val.map (homOfLE inf_le_right).op (sf j)
    rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality, hf i j]
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' U V (fun i => homOfLE (hUV i)) hcover sf hc
  refine ⟨(freeOpenEquiv R M V).symm s, fun i => ?_⟩
  apply (freeOpenEquiv R M (U i)).injective
  rw [freeOpenEquiv_naturality]
  exact (congrArg (M.val.map (homOfLE (hUV i)).op)
    ((freeOpenEquiv R M V).apply_symm_apply s)).trans (hs i)

end
end PiExponent.GeometrySupport.CechOne

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechHigher
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem map_injective {N : SheafOfModules.{u} R} (g : M ⟶ N) [Mono g] {q : ℕ} :
    Function.Injective (map R U M g (q := q)) := by
  intro c e h
  funext t
  exact (cancel_mono g).mp (congrFun h t)

theorem lift_kernel_cochain (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ} (c : Cochain R U S.X₂ q)
    (hc : map R U S.X₂ S.g c = 0) :
    ∃ b : Cochain R U S.X₁ q, map R U S.X₁ S.f b = c := by
  let : Mono S.f := hS.mono_f
  have hz (t : Fin (q + 1) → J) : c t ≫ S.g = 0 := congrFun hc t
  exact ⟨fun t => hS.exact.lift (c t) (hz t),
    funext (fun t => hS.exact.lift_f (c t) (hz t))⟩

theorem restrict_cochain_congr {q : ℕ} (c : Cochain R U M q)
    {t t' : Fin (q + 1) → J} (ht : t = t') {W : Opens X}
    (h : W ≤ intersection U t) (h' : W ≤ intersection U t') :
    restrictHom R h (c t) = restrictHom R h' (c t') := by
  subst t'
  rfl

theorem sectionZero_compatible (c : Cochain R U M 0)
    (hc : differential R U M c = 0) (i j : J) :
    restrictHom R inf_le_left (sectionZero R U M c i) =
      restrictHom R inf_le_right (sectionZero R U M c j) := by
  let W := U i ⊓ U j
  let f : Fin 2 → J := Fin.cons i (fun _ => j)
  have hf : ∀ l, W ≤ U (f l) := by
    intro l
    cases l using Fin.cases with
    | zero => exact inf_le_left
    | succ l => exact inf_le_right
  have h := evaluate_differential R U M W f hf c
  rw [hc] at h
  have h' := congrFun h (Fin.cons 0 (fun _ => 1))
  have hz : evaluate R U M W f hf (0 : Cochain R U M 1)
      (Fin.cons 0 (fun _ => 1)) = 0 := comp_zero
  rw [hz, scalar_differential_zero_degree] at h'
  have he := (sub_eq_zero.mp h'.symm).symm
  have h0 : f ∘ (fun _ : Fin 1 => (0 : Fin 2)) = (fun _ => i) := by
    funext k
    rfl
  have h1 : f ∘ (fun _ : Fin 1 => (1 : Fin 2)) = (fun _ => j) := by
    funext k
    rfl
  calc
    restrictHom R inf_le_left (sectionZero R U M c i) =
        evaluate R U M W f hf c (fun _ => 0) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact (restrict_cochain_congr R U M c h0 _ _).symm
    _ = evaluate R U M W f hf c (fun _ => 1) := he
    _ = restrictHom R inf_le_right (sectionZero R U M c j) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact restrict_cochain_congr R U M c h1 _ _

theorem glue_zero_cocycle (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ g : freeOpen R V ⟶ M,
      ∀ i, restrictHom R (hUV i) g = sectionZero R U M c i := by
  exact hom_glue R U V hUV hcover M (sectionZero R U M c)
    (sectionZero_compatible R U M c hc)

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_FreeCechSections
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def tupleNatEquiv (F : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)) ⟶ F) ≃
      (∀ t : Fin (q + 1) → J, F.obj (op (intersection U t))) where
  toFun a t := a.app _ (canonicalTuple U t)
  invFun s :=
    { app W := ↾fun v =>
        F.map (homOfLE (le_iInf fun i => (v i).property)).op (s (fun i => (v i).val))
      naturality W V f := by
        ext v
        let t : Fin (q + 1) → J := fun i => (v i).val
        let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
        exact F.map_comp_apply (homOfLE h).op f (s t) }
  left_inv a := by
    ext W v
    let t : Fin (q + 1) → J := fun i => (v i).val
    let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
    have he : (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).map
        (homOfLE h).op) (canonicalTuple U t) = v := by
      funext i
      apply Subtype.ext
      rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalTuple U t)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext t
    change F.map (𝟙 (op (intersection U t))) (s t) = s t
    rw [CategoryTheory.Functor.map_id]
    rfl

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

def sectionValuesEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃
    (∀ t : Fin (q + 1) → J, M.val.obj (op (intersection U t))) :=
  ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeHomEquiv).trans (tupleNatEquiv U _ q)

def sectionsEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃ Cochain R U M q :=
  (sectionValuesEquiv U R M q).trans
    (Equiv.piCongrRight fun t => (freeOpenEquiv R M (intersection U t)).symm)

theorem sectionsEquiv_apply (q : ℕ) (f : freeTerm U R q ⟶ M) (t : Fin (q + 1) → J) :
    sectionsEquiv U R M q f t = generator U R t ≫ f := by
  apply (freeOpenEquiv R M (intersection U t)).injective
  simp only [sectionsEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.apply_symm_apply]
  let g := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f
  change (PresheafOfModules.freeHomEquiv g).app _ (canonicalTuple U t) =
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) (generator U R t ≫ f))
  symm
  have hs := congrArg PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left
      ((PresheafOfModules.free R.obj).map (tupleEmbedding U t)) f)
  have hf := congrArg yonedaEquiv
    ((PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
      (tupleEmbedding U t) g)
  exact hs.trans (hf.trans (yonedaEquiv_comp (tupleEmbedding U t)
    (PresheafOfModules.freeHomEquiv g)))

theorem tupleEmbedding_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    tupleEmbedding U t ≫ (tuplePresheaf (coverVertices U)).δ k =
      yoneda.map (homOfLE (faceLE U t k)) ≫ tupleEmbedding U (t ∘ k.succAbove) := by
  simp only [tupleEmbedding]
  ext W v
  funext i
  apply Subtype.ext
  rfl

theorem generator_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    generator U R t ≫ freeFace U R q k =
      freeOpenMap R (homOfLE (faceLE U t k)) ≫ generator U R (t ∘ k.succAbove) := by
  simp only [generator, freeFace]
  let F : ((Opens X)ᵒᵖ ⥤ Type u) ⥤ SheafOfModules.{u} R :=
    PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
  change F.map (tupleEmbedding U t) ≫ F.map ((tuplePresheaf (coverVertices U)).δ k) =
    F.map (yoneda.map (homOfLE (faceLE U t k))) ≫ F.map (tupleEmbedding U (t ∘ k.succAbove))
  exact (F.map_comp _ _).symm.trans
    ((congrArg (fun f => F.map f) (tupleEmbedding_face U t k)).trans (F.map_comp _ _))

theorem sectionsEquiv_boundary (q : ℕ) (f : freeTerm U R q ⟶ M) :
    sectionsEquiv U R M (q + 1) (boundary U R q ≫ f) =
      differential R U M (sectionsEquiv U R M q f) := by
  funext t
  rw [sectionsEquiv_apply, ← Category.assoc, boundary_eq_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, generator_face,
    Category.assoc, CechHigher.differential, sectionsEquiv_apply, CechOne.restrictHom]

theorem hasPrimitives_of_exact [Injective M] (q : ℕ)
    (hexact : (termShortComplex U R q).Exact) : HasPrimitives R U M q := by
  intro c hc
  let f := (sectionsEquiv U R M (q + 1)).symm c
  have hf : boundary U R (q + 1) ≫ f = 0 := by
    apply (sectionsEquiv U R M (q + 2)).injective
    rw [sectionsEquiv_boundary]
    have he : sectionsEquiv U R M (q + 1) f = c :=
      (sectionsEquiv U R M (q + 1)).apply_symm_apply c
    rw [he, hc]
    funext t
    rw [sectionsEquiv_apply, comp_zero]
    rfl
  let g : freeTerm U R q ⟶ M := hexact.descToInjective f hf
  refine ⟨sectionsEquiv U R M q g, ?_⟩
  rw [← sectionsEquiv_boundary]
  exact (congrArg (fun f : freeTerm U R (q + 1) ⟶ M => sectionsEquiv U R M (q + 1) f)
    (hexact.comp_descToInjective f hf)).trans
      ((sectionsEquiv U R M (q + 1)).apply_symm_apply c)

theorem injective_hasPrimitives [Injective M] (q : ℕ) : HasPrimitives R U M q := by
  apply hasPrimitives_of_exact U R M q
  have h := freeSheafComplex_exact R (coverVertices U) q
  exact (HomologicalComplex.exactAt_iff'
    (K := freeSheafComplex R (coverVertices U)) (i := q + 2) (j := q + 1) (k := q)
    (by simp) (by simp)).mp h

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechLinear
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.CechLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped BigOperators AlgebraicGeometry

universe v
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type v} [Field K]

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup

attribute [local instance] freeOpenHomModule

variable (ρ : K →+* Γ(X, ⊤)) (M : X.Modules)

variable {M} {N P : X.Modules}

theorem mapLinear_differential (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g (q + 1) (differentialLinear U ρ M q c) =
      differentialLinear U ρ N q (mapLinear U ρ g q c) :=
  CechHigher.map_differential X.ringCatSheaf U M g c

variable (M)

theorem boundaryToCycles_surjective [hM : Injective M] (q : ℕ) :
    Function.Surjective (boundaryToCycles U ρ M q) := by
  intro c
  obtain ⟨b, hb⟩ := @FreeCechSections.injective_hasPrimitives _ J U X.ringCatSheaf M hM q
    c.val c.property
  exact ⟨b, Subtype.ext hb⟩

def primitive [Injective M] (q : ℕ) :
    cycles U ρ M (q + 1) →ₗ[K] Cochain U ρ M q :=
  Classical.choose ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))

@[simp] theorem boundaryToCycles_primitive [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    boundaryToCycles U ρ M q (primitive U ρ M q c) = c := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))) c

@[simp] theorem primitive_spec [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    CechHigher.differential X.ringCatSheaf U M (primitive U ρ M q c) = c.val :=
  congrArg Subtype.val (boundaryToCycles_primitive U ρ M q c)

end
end PiExponent.GeometrySupport.CechLinear

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_CechZero
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechZero

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry

variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤)) (M : X.Modules)

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

def augmentationLinear (V : X.Opens) (hUV : ∀ i, U i ≤ V) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) →ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  refine {
    toFun := fun f => ⟨CechHigher.augmentation X.ringCatSheaf U M V hUV f,
      CechHigher.augmentation_closed X.ringCatSheaf U M V hUV f⟩
    map_add' := ?_
    map_smul' := ?_ }
  · intro f g
    apply Subtype.ext
    funext t
    exact CechOne.restrictHom_add X.ringCatSheaf _ f g
  · intro r f
    apply Subtype.ext
    funext t
    exact Linear.comp_smul (C := X.Modules) _ _ _
      (freeOpenMap X.ringCatSheaf
        (homOfLE ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))))) (ρ r) f

@[simp] theorem augmentationLinear_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (f : schemeFreeOpen V ⟶ M) :
    (augmentationLinear U ρ M V hUV f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

end PiExponent.GeometrySupport.CechZero

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologyFiniteCharts
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial HomogeneousLocalization
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K]

open PiExponentSeshadri.Frames

lemma normalized_evalAway_polyToChart {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
      (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))).comp
      (polyToChart i) = eval₂Hom k (fun j : ChartVariables i => a j) := by
  let F := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : R)))
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_C]
    change F (chartConstants i r) = k r
    exact evalAway_constants i k a hi r
  · intro j
    simp only [RingHom.comp_apply, polyToChart, eval₂Hom_X']
    change F (chartCoordinate i j.val) = a j.val
    have H := evalAway_mk_clear (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (isHomogeneous_X K i)
      (show IsUnit ((eval₂Hom k a) (MvPolynomial.X i)) by simpa only [eval₂Hom_X',hi] using
        (isUnit_one : IsUnit (1 : R))) 1 (X j.val) (by simpa using isHomogeneous_X K j.val)
    simpa only [chartCoordinate, eval₂Hom_X',hi,one_pow,mul_one] using H

theorem finite_sectionsMorphism_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : σ) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).Finite := by
  let V := projectiveCoordinateCover (K := K) (σ := σ)
  let U := SectionOpens.isoOpen (s i)
  let k' := U.ι.appTop.hom.comp k
  let a : σ → Γ(U.toScheme,⊤) := fun j => coefficient (sectionFrame (s i))
    (restrictSection U.ι (s j))
  have hi : a i = 1 := sectionFrame_normalized (s i)
  let f := evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k' a) (MvPolynomial.X i)
    (by simpa only [eval₂Hom_X',hi] using (isUnit_one : IsUnit (1 : Γ(U.toScheme,⊤))))
  let g : U.toScheme ⟶ Spec (CommRingCat.of (Away (homogeneousSubmodule σ K) (MvPolynomial.X i))) :=
    U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)
  have hV : IsOpenImmersion (V.f i) := by
    exact inferInstanceAs (IsOpenImmersion
      (Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)))
  have H : IsPullback g U.ι (V.f i) (sectionsMorphism k s hs) := by
    apply @IsOpenImmersion.isPullback _ _ _ _ g U.ι (V.f i)
      (sectionsMorphism k s hs) (inferInstanceAs (IsOpenImmersion U.ι)) hV
    · exact (sectionsMorphism_local k s hs i).trans (Category.assoc _ _ _).symm
    · change _ ⁻¹ᵁ (Proj.awayι (homogeneousSubmodule σ K) (MvPolynomial.X i) _ _).opensRange = _
      erw [Proj.opensRange_awayι, sectionsMorphism_preimage, Scheme.Opens.opensRange_ι]
  have hg : IsFinite g := by
    exact MorphismProperty.of_isPullback H.flip (inferInstance : IsFinite (sectionsMorphism k s hs))
  refine ⟨isAffine_of_isAffineHom g, ?_⟩
  have hf := (@affine_evaluation_finite _ _ U.toScheme f hg).comp (RingHom.Finite.of_surjective
    (polyToChart (R := K) i) (polynomialChartEquiv (R := K) i).symm.surjective)
  rwa [normalized_evalAway_polyToChart k' a i hi] at hf

theorem finite_pencil_chart {X : Scheme} {M : X.Modules}
    (k : K →+* Γ(X,⊤)) (s : Bool → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (i : Bool) :
    IsAffine (SectionOpens.isoOpen (s i)).toScheme ∧
    (Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i))))).Finite := by
  obtain ⟨hA,hf⟩ := finite_sectionsMorphism_chart k s hs i
  refine ⟨hA, ?_⟩
  have h := hf.comp (RingHom.Finite.of_surjective
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom
    (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.surjective)
  have he : (eval₂Hom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (fun j : ChartVariables i => coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)))).comp
      (MvPolynomial.uniqueAlgEquiv K (ChartVariables i)).symm.toRingHom =
      Polynomial.eval₂RingHom ((SectionOpens.isoOpen (s i)).ι.appTop.hom.comp k)
      (coefficient (sectionFrame (s i))
        (restrictSection (SectionOpens.isoOpen (s i)).ι (s (!i)))) := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPolynomial.uniqueAlgEquiv]
    · have hd : (default : ChartVariables i).val = !i :=
        congrArg Subtype.val (Subsingleton.elim (default : ChartVariables i)
          ⟨!i, by cases i <;> decide⟩)
      simpa [MvPolynomial.uniqueAlgEquiv] using congrArg
        (fun j => coefficient (sectionFrame (s i))
          (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))) hd
  rwa [he] at h
end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomology
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}}

def BaseSections.globalIntersection [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) :
    Sections k L.sheaf ⊤ →ₗ[K] ↥(twoBaseIntersection k L.sheaf U V) :=
  (res k L.sheaf (show U ⊓ V ≤ ⊤ from le_top)).codRestrict _ (by
    intro m
    exact ⟨⟨res k L.sheaf (show U ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_left le_top m⟩,
      ⟨res k L.sheaf (show V ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_right le_top m⟩⟩)

lemma BaseSections.globalIntersection_injective [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) [Nonempty (U ⊓ V : X.Opens)] :
    Function.Injective (globalIntersection k L U V) := by
  intro a b h
  exact L.restriction_injective (homOfLE (show U ⊓ V ≤ ⊤ from le_top))
    (congrArg Subtype.val h)

def BaseSections.globalSectionsLinear (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def BaseSections.cohomologyZero (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalSectionsLinear M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_ProjectiveFramedCech
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectiveLine.boolChartVariablesUnique _root_.OAI.PiExponent.ProjectiveLine.chartRingEquiv_isIso _root_.OAI.PiExponent.ProjectiveMonomialCohomology.degreeZero_finite _root_.OAI.PiExponent.ProjectiveMonomialCohomology.negativeCycles_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.allNonnegative_finite _root_.OAI.PiExponent.ProjectiveMonomialFinite.monomial_subsingleton _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.Projective.boolChartUnique _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def coordinateFramedOverlap (i : σ) (a : Finset (ChartVariables i)) :
    (schemeFreeOpen_p0 (coordinateFiniteOpen M s i a) ⟶ N) →+ Laurent σ K d :=
  framedLaurentOverlap _ N i d a (restrictOpenFrame inf_le_left (e i))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

attribute [local irreducible] coordinateFramedOverlap

def coordinateFramedTuple (q : ℕ) (t : Fin (q + 1) → σ) :
    (schemeFreeOpen_p0
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) →+
      Laurent σ K d :=
  (coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationNonaffine
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationModel
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponent.CurveZeroPole
universe u
variable {F E : Type u} [Field F] [Field E] [Algebra F E]
variable (f : E) (hf : Transcendental F f)
variable [CharZero F] [FiniteDimensional (IntermediateField.adjoin F {f}) E]

theorem parameterCurve_not_isAffine : ¬ IsAffine (parameterCurve f hf) := by
  intro haff
  let X := parameterCurve f hf
  let p := parameterCurveStructureMap f hf
  have : IsAffine X := haff
  have : IsFinite p := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  let : Algebra F Γ(X,⊤) :=
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).toAlgebra
  have : Module.Finite F Γ(X,⊤) :=
    p.finite_appTop.comp (RingHom.Finite.of_surjective
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
      (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : IsArtinianRing Γ(X,⊤) := IsArtinianRing.of_finite F Γ(X,⊤)
  have : IsLocallyArtinian (Spec Γ(X,⊤)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : T1Space (Spec Γ(X,⊤)) := inferInstance
  have : T1Space X := X.isoSpec.hom.isEmbedding.t1Space
  exact (parameterCurve_isClosed_iff_ne_generic f hf
    (genericPoint (parameterCurve f hf))).mp isClosed_singleton rfl

end PiExponent.CurveNormalizationModel

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveNormalizationUnit
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X Y : Scheme.{0}}

def unitMap (f : Y ⟶ X) : structureSheaf X ⟶
    (Scheme.Modules.pushforward f).obj (structureSheaf Y) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

theorem unitMap_mono (f : Y ⟶ X) [IsReduced X] [QuasiCompact f] [IsDominant f] :
    Mono (unitMap f) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  have h : Mono (unitMap f).val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    exact f.app_injective U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map h

theorem unitMap_restrict_isIso (f : Y ⟶ X) (U : X.Opens) [IsIso (f ∣_ U)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (unitMap f)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro V
  have h := morphismRestrict_app f U V
  have hiso : IsIso ((f ∣_ U).app V) := by infer_instance
  have : IsIso (f.app (U.ι ''ᵁ V) ≫
      Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op) := by
    rw [← h]
    exact hiso
  have : IsIso (f.app (U.ι ''ᵁ V)) :=
    (isIso_comp_right_iff (f.app (U.ι ''ᵁ V))
      (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op)).mp inferInstance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (f.app (U.ι ''ᵁ V))

theorem unitMap_isoOpen_ne_bot (f : Y ⟶ X) (U : X.Opens)
    (hU : U ≠ ⊥) [IsIso (f ∣_ U)] : isoOpen (unitMap f) ≠ ⊥ := by
  have hle : U ≤ isoOpen (unitMap f) := by
    intro x hx
    exact (mem_isoOpen_iff _ x).mpr ⟨U,hx,unitMap_restrict_isIso f U⟩
  intro h
  exact hU (le_antisymm (h ▸ hle) bot_le)

end PiExponent.CurveNormalizationDegree

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveSectionsPullback
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K σ : Type} [CommRing K] {X Y : Scheme.{0}}

theorem sectionsMorphism_pullback {M : X.Modules} (k : K →+* Γ(X,⊤))
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (f : Y ⟶ X) :
    f ≫ sectionsMorphism k s hs =
      sectionsMorphism (f.appTop.hom.comp k) (fun i => pullbackSection f (s i))
        (pullback_sections_cover s hs f) := by
  let t (i : σ) := pullbackSection f (s i)
  let ht := pullback_sections_cover s hs f
  have hc : (⨆ i, f ⁻¹ᵁ SectionOpens.isoOpen (s i)) = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup,hs,Scheme.Hom.preimage_top]
  apply (Y.openCoverOfIsOpenCover (fun i => f ⁻¹ᵁ SectionOpens.isoOpen (s i)) hc).hom_ext
  intro i
  let U := SectionOpens.isoOpen (s i)
  obtain ⟨e,he⟩ := exists_restricted_pullback_frame_all f U (sectionFrame (s i))
  have hi : coefficient e (restrictSection (f ⁻¹ᵁ U).ι (t i)) = 1 := by
    rw [he,sectionFrame_normalized,map_one]
  change (f ⁻¹ᵁ U).ι ≫ (f ≫ sectionsMorphism k s hs) =
    (f ⁻¹ᵁ U).ι ≫ sectionsMorphism (f.appTop.hom.comp k) t ht
  erw [← Category.assoc, ← morphismRestrict_ι f U, Category.assoc,
    sectionsMorphism_local k s hs i, coordinatesMap_natural,
    sectionsMorphism_frame _ t ht (f ⁻¹ᵁ U).ι e i hi]
  congr 1
  · rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
      morphismRestrict_ι f U, Scheme.Hom.comp_appTop]
    rfl
  · exact (funext fun j => he (s j)).symm
end
end PiExponentSeshadri.Projective

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveFinitePencil
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.GlueGlobalGenerators.instIsFiniteTypeOpensCarrierCarrierCommRingCatGlobalGeneratorsOfFiniteOfToScheme _root_.OAI.PiExponent.NegativeTwistPresentations.presentationMap_epi _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_integral _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_irreducible _root_.OAI.PiExponent.ProjectiveO1.projectiveSpace_reduced _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.ProjectivePencil

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry PiExponentSeshadri.Projective


variable {K σ : Type} [CommRing K] {X : Scheme.{0}}

def lineBundle (f : X ⟶ ProjectiveO1.projectiveSpace K σ) : LineBundle X :=
  (ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback f

def coordinateSection (f : X ⟶ ProjectiveO1.projectiveSpace K σ) (i : σ) :
    O X ⟶ (lineBundle f).sheaf :=
  pullbackSection f (ProjectiveO1.coordinateSection (R := K) i)

theorem sections_cover (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (coordinateSection f i)) = ⊤ :=
  pullback_sections_cover ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f

theorem sectionsMorphism_eq (f : X ⟶ ProjectiveO1.projectiveSpace K σ) :
    sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f) = f := by
  have h := sectionsMorphism_pullback
    (M := (ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf)
    (ProjectiveO1.scalars (R := K) (σ := σ))
    ProjectiveO1.coordinateSection ProjectiveO1.coordinateSection_cover f
  rw [ProjectiveO1.coordinate_sectionsMorphism_identity, Category.comp_id] at h
  exact h.symm

instance sectionsMorphism_isFinite (f : X ⟶ ProjectiveO1.projectiveSpace K σ)
    [IsFinite f] : IsFinite (sectionsMorphism (scalars f) (coordinateSection f) (sections_cover f)) := by
  rw [sectionsMorphism_eq]
  infer_instance

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

end PiExponent.ProjectivePencil

end

end OAI
end


