-- Prove2me | Definitions.Def_OAIQ068A013
-- name    : OAIQ068A013
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:43:49.524927+00:00
-- url     : https://prove2.me/theorems/ae242219-7968-4245-b1aa-9af38be4a221
-- title:
--   Definitions bundle OAIQ068A013 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 82 declarations of OpenAI's Lean: 11 definitions, 8 instances and 63 theorems. The definitions and types are `OAI.PiExponent.AdmissibleParameters.curveCenters`, `OAI.PiExponent.AlgebraicJetPackets.triangularEquiv`, `OAI.PiExponent.CompactLogJetIdeal.point`, `OAI.PiExponent.CompactLogJetIdeal.structureMap`, `OAI.PiExponent.CurveProductFormula.principalDivisor`, `OAI.PiExponent.GlobalSectionClearing.openSectionsCongr`, `OAI.PiExponent.WeightedCompactification.projection`, `OAI.PiExponentSeshadri.Geometry.GlobalSections`, `OAI.PiExponentSeshadri.Geometry.pullbackFrame`, `OAI.PiExponentSeshadri.Geometry.sectionOpen`, `OAI.PiExponentSeshadri.ReesGrading.principalMap`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AffineBlowupUniversal`, `PiExponent_Ampleness_BlowupIdeal`, `PiExponent_Ampleness_GlobalBlowupGluing`, `PiExponent_Ampleness_ReesPrincipalLift`, `PiExponent_Ampleness_ReesPushdown`, `PiExponent_Ampleness_ReesUniversalUniqueness`, `PiExponent_Approximation_FrameSections`, `PiExponent_Approximation_FramedPullback`, `PiExponent_Approximation_GlobalSectionClearing`, `PiExponent_Approximation_IntegralLineSections`, `PiExponent_Approximation_PowerSectionExtension`, `PiExponent_Approximation_PushforwardTensor`, `PiExponent_Approximation_SectionDivision`, `PiExponent_Approximation_SectionOpens`, `PiExponent_Approximation_SectionPullback`, `PiExponent_Approximation_TensorPure`, `PiExponent_Approximation_WeightedAffineParametrization`, `PiExponent_Approximation_WeightedCompactificationGeometry`, `PiExponent_Approximation_WeightedCompactificationImmersion`, `PiExponent_Cohomology_PencilCohomologySections`, `PiExponent_Geometry_AdmissibleCurveInequality`, `PiExponent_Geometry_CurveProductFormula`, `PiExponent_Geometry_LineBundleGluingSections`, `PiExponent_Geometry_LineBundleTensor`, `PiExponent_Geometry_PolynomialProjectiveStructure`, `PiExponent_Geometry_ProjectiveCharts`, `PiExponent_Geometry_ProjectiveCoordinateValues`, `PiExponent_Geometry_ProjectiveEmbeddingCharts`, `PiExponent_Geometry_WeightedProjectiveStructure`, `PiExponent_Jets_AlgebraicJetPackets`, `PiExponent_Jets_CompactJetIdeal`, `PiExponent_Jets_CompactJetPolynomial`, `PiExponent_Jets_CompactLogJetIdeal`, `PiExponent_Polynomials_SurjectiveGradedMap`.
--
--   **Imports.** It imports the bundles `OAIQ068A000`, `OAIQ068A001`, `OAIQ068A002` and `OAIQ068A003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A020`, `OAIQ068A021`, `OAIQ068A022`, `OAIQ068A023`, `OAIQ068A024`, `OAIQ068A025` and `OAIQ068A026`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A000
import Definitions.Def_OAIQ068A001
import Definitions.Def_OAIQ068A002
import Definitions.Def_OAIQ068A003

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleTensor
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

variable (X : Scheme)

abbrev GlobalSections (M : X.Modules) := structureSheaf X ⟶ M

def sectionOpen {M : X.Modules} (s : GlobalSections X M) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)), U

end Geometry

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FrameSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Frames

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleSectionEquiv_scalar {M : X.Modules} (f : Γ(X, ⊤)) (s : O X ⟶ M) :
    moduleSectionEquiv M (scalarEnd f ≫ s) = f • moduleSectionEquiv M s := by
  change s.app ⊤ (endValue (scalarEnd f)) = f • s.app ⊤ (1 : Γ(X, ⊤))
  rw [endValue_scalarEnd]
  have h := s.app_smul (r := f) (x := (1 : Γ(X, ⊤)))
  change s.app ⊤ (f * 1 : Γ(X, ⊤)) = f • s.app ⊤ (1 : Γ(X, ⊤)) at h
  simpa only [mul_one] using h

lemma openSectionEquiv_scalar (M : X.Modules) (U : X.Opens)
    (f : Γ(U.toScheme, ⊤)) (s : O U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv M U (scalarEnd f ≫ s) = U.topIso.hom f • openSectionEquiv M U s := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (moduleSectionEquiv (M.restrict U.ι) (scalarEnd f ≫ s)) = _
  rw [moduleSectionEquiv_scalar]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv f • (show Γ(M, U.ι ''ᵁ ⊤) from moduleSectionEquiv (M.restrict U.ι) s)) = _
  rw [M.map_smul, U.ι_appIso]
  rfl

lemma openSectionEquiv_restrict_value (M : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U s) =
      s.app W (1 : Γ(U.toScheme, W)) := by
  have h := section_value_natural s (homOfLE (show W ≤ ⊤ from le_top))
  change M.presheaf.map (U.ι.opensFunctor.map (homOfLE (show W ≤ ⊤ from le_top))).op
    (s.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _ at h
  change M.presheaf.map (homOfLE (U.ι_image_le W)).op
    (M.presheaf.map (eqToHom U.ι_image_top.symm).op (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

lemma image_section_extension (M : X.Modules) (U : X.Opens)
    (s t : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens)
    (f : Γ(W.toScheme, ⊤))
    (h : restrictSection W.ι t = scalarEnd f ≫ restrictSection W.ι s) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U t) =
      (U.ι.appIso W).inv (W.topIso.hom f) • M.presheaf.map (homOfLE (U.ι_image_le W)).op
        (openSectionEquiv M U s) := by
  have hh := congrArg (openSectionEquiv (M.restrict U.ι) W) h
  rw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict] at hh
  rw [openSectionEquiv_restrict_value, openSectionEquiv_restrict_value]
  exact hh

end PiExponentSeshadri.Frames

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace IdealPullback

open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

lemma comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V.1 U.1 e).hom := by
  suffices hh : ((I.comap f).ideal U).map U.1.topIso.inv.hom =
      ((I.ideal V).map (f.appLE V.1 U.1 e).hom).map U.1.topIso.inv.hom by
    have hh' := congrArg (Ideal.map U.1.topIso.hom.hom) hh
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id, CommRingCat.hom_id,
      Ideal.map_id] using hh'
  rw [← comap_ι_top, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.Hom.resLE_comp_ι f e, Scheme.IdealSheafData.comap_comp,
    comap_top, comap_ι_top, Ideal.map_map, Ideal.map_map]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.hom_comp,
    Iso.inv_hom_id_assoc]

end IdealPullback

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPushdown
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading

section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance instIsScalarTowerSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNat : IsScalarTower R (piece I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := piece I 0) (A := reesAlgebra I)
    (fun _ => rfl)

instance instFiniteTypeSubtypePolynomialMemSubalgebraReesAlgebraSubmodulePieceOfNatNatOfIsNoetherianRing [IsNoetherianRing R] : Algebra.FiniteType (piece I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (piece I 0) (reesAlgebra I)

instance projection_proper [IsNoetherianRing R] : IsProper (projection I) := by
  have hP : IsProper (Proj.toSpecZero (piece I)) := inferInstance
  have hS : IsIso (Spec.map (zeroIso I).hom) := inferInstance
  have hQ : IsProper (Spec.map (zeroIso I).hom) := by infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ hP hQ

end

open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesPrincipalLift
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.BlowupLift
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsLeftRegular r)

include hr in

lemma coefficients_span : Ideal.span (Set.range (coefficient I f r hI)) = ⊤ := by
  let K : Ideal S := Ideal.span (Set.range (coefficient I f r hI))
  have hmap : I.map f ≤ Submodule.map (LinearMap.mulLeft S r) K := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change f a ∈ Submodule.map (LinearMap.mulLeft S r) K
    exact ⟨coefficient I f r hI ⟨a, ha⟩,
      Ideal.subset_span (Set.mem_range_self _), mul_coefficient I f r hI ⟨a, ha⟩⟩
  have hmem : r ∈ Submodule.map (LinearMap.mulLeft S r) K := by
    apply hmap
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton r)
  obtain ⟨s, hs, hrs⟩ := hmem
  have hs1 : s = 1 := hr (by simpa using hrs)
  refine Ideal.eq_top_of_isUnit_mem (I := K) ?_ isUnit_one
  exact hs1 ▸ hs

end PiExponentSeshadri.BlowupLift

namespace PiExponentSeshadri.ReesGrading

section
open Polynomial
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable {S : Type v} [CommRing S] (f : R →+* S) (r : S)
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

lemma principalToLocalization_generator (a : I) :
    principalToLocalization I f r (generator I a) =
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by
  change (Polynomial.eval₂RingHom ((algebraMap S (Localization.Away r)).comp f)
    (IsLocalization.Away.invSelf r)) (monomial 1 a.val) = _
  simp only [coe_eval₂RingHom, eval₂_monomial, RingHom.comp_apply, pow_one]
  rw [← BlowupLift.mul_coefficient I f r hI a, map_mul]
  calc _ = (algebraMap S (Localization.Away r) r * IsLocalization.Away.invSelf r) *
      algebraMap S (Localization.Away r) (BlowupLift.coefficient I f r hI a) := by ring
       _ = _ := by rw [IsLocalization.Away.mul_invSelf, one_mul]

include hI in
lemma principalToLocalization_range (p : reesAlgebra I) :
    ∃ s : S, algebraMap S (Localization.Away r) s = principalToLocalization I f r p := by
  have hp : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hp using Algebra.adjoin_induction with
  | mem p hp =>
    obtain ⟨a, rfl⟩ := hp
    exact ⟨BlowupLift.coefficient I f r hI a, (principalToLocalization_generator I f r hI a).symm⟩
  | algebraMap s => exact ⟨f s, (principalToLocalization_base I f r s).symm⟩
  | add p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s+t, by rw [map_add, hs, ht, map_add]⟩
  | mul p q _ _ hp hq =>
    obtain ⟨s, hs⟩ := hp
    obtain ⟨t, ht⟩ := hq
    exact ⟨s*t, by rw [map_mul, hs, ht, map_mul]⟩

def principalMap : reesAlgebra I →+* S where
  toFun p := Classical.choose (principalToLocalization_range I f r hI p)
  map_zero' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 0), map_zero, map_zero])
  map_one' := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI 1), map_one, map_one])
  map_add' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p+q)), map_add,
      map_add, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])
  map_mul' p q := principalLocalization_injective r hr (by
    rw [Classical.choose_spec (principalToLocalization_range I f r hI (p*q)), map_mul,
      map_mul, Classical.choose_spec (principalToLocalization_range I f r hI p),
      Classical.choose_spec (principalToLocalization_range I f r hI q)])

lemma principalMap_spec (p : reesAlgebra I) :
    algebraMap S (Localization.Away r) (principalMap I f r hI hr p) =
      principalToLocalization I f r p :=
  Classical.choose_spec (principalToLocalization_range I f r hI p)

lemma principalMap_base (s : R) :
    principalMap I f r hI hr (algebraMap R (reesAlgebra I) s) = f s := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_base]

lemma principalMap_generator (a : I) :
    principalMap I f r hI hr (generator I a) = BlowupLift.coefficient I f r hI a := by
  apply principalLocalization_injective r hr
  rw [principalMap_spec, principalToLocalization_generator]

lemma principalMap_irrelevant :
    (HomogeneousIdeal.irrelevant (piece I)).toIdeal.map (principalMap I f r hI hr) = ⊤ := by
  rw [eq_top_iff, ← BlowupLift.coefficients_span I f r hI hr.left]
  apply Ideal.span_le.mpr
  rintro s ⟨a, rfl⟩
  rw [← principalMap_generator I f r hI hr]
  apply Ideal.mem_map_of_mem
  exact HomogeneousIdeal.mem_irrelevant_of_mem (piece I) (by decide : 0 < (1 : ℕ))
    (generator_mem I a)

end

open CategoryTheory AlgebraicGeometry
universe u

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesUniversalUniqueness
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
open Polynomial HomogeneousLocalization
universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (a : I)
variable {B : Type v} [CommRing B] (f : R →+* B)

lemma base_pow_mul_mk (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartBase I a (a.val ^ n) *
        HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp =
      chartBase I a (evaluation I p) := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_base, chartMap_mk]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I p) ⟨a.val ^ n, n, rfl⟩

end PiExponentSeshadri.ReesGrading

namespace PiExponentSeshadri.ReesGrading
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma base_generator_comm (a b : I) :
    algebraMap R (reesAlgebra I) a.val * generator I b =
      algebraMap R (reesAlgebra I) b.val * generator I a := by
  apply Subtype.ext
  change C a.val * monomial 1 b.val = C b.val * monomial 1 a.val
  simp only [C_mul_monomial, mul_comm a.val b.val]

lemma chartHom_ext {S : Type*} [CommRing S] (a : I)
    (g h : chart I a →+* S) (he : g.comp (chartBase I a) = h.comp (chartBase I a))
    (hr : IsRegular (g (chartBase I a a.val))) : g = h := by
  have hb (s : R) : g (chartBase I a s) = h (chartBase I a s) := RingHom.congr_fun he s
  ext x
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  apply (hr.pow n).left
  have h₁ := congrArg g (base_pow_mul_mk I a n p hp)
  have h₂ := congrArg h (base_pow_mul_mk I a n p hp)
  simpa only [map_mul, map_pow, hb] using h₁.trans ((hb ((evaluation I) p)).trans h₂.symm)

open SpecMaps

lemma chart_scheme_ext {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ Spec (CommRingCat.of (chart I a)))
    (he : g ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) =
      h ≫ Spec.map (CommRingCat.ofHom (chartBase I a)))
    (hr : IsRegular (coordinate g (chartBase I a a.val))) : g = h := by
  apply coordinate_ext
  apply CommRingCat.hom_ext
  apply chartHom_ext I a _ _ _ hr
  have hc := congrArg coordinate he
  simp only [coordinate_comp_spec] at hc
  exact congrArg CommRingCat.Hom.hom hc

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionOpens
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace SectionOpens

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_postcomp (f : M ⟶ N) (e : N ≅ P) :
    isoOpen (f ≫ e.hom) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f) ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

end SectionOpens

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_IntegralLineSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h
end Frames

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PowerSectionExtension
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
@[simp] lemma coefficient_scalarEnd {X : Scheme} {M : X.Modules}
    (e : M ≅ O X) (a : Γ(X, ⊤)) :
    coefficient e (scalarEnd a ≫ e.inv) = a := by
  simp only [coefficient, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    endValue_scalarEnd]
end Frames

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AffineBlowupUniversal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.IdealPullback
noncomputable section
open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

lemma specIdeal_coordinate {Y : Scheme} [IsAffine Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) :
    ((specIdeal I).comap f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      I.map (SpecMaps.coordinate f).hom := by
  rw [comap_top, specIdeal_top, Ideal.map_map]
  rfl

end
end PiExponentSeshadri.IdealPullback

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupGluing
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealPullback
open CategoryTheory AlgebraicGeometry
variable {X : Scheme.{0}} [IsAffine X]

lemma specIdeal_comap_toSpec (I : X.IdealSheafData) :
    (specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩)).comap X.toSpecΓ = I := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, Scheme.toSpecΓ_appTop, Ideal.map_map]
  change Ideal.map ((Scheme.ΓSpecIso Γ(X, ⊤)).hom.hom.comp
    (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom) _ = _
  simp only [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id, Ideal.map_id]

lemma comap_isoSpec_inv (I : X.IdealSheafData) :
    I.comap X.isoSpec.inv = specIdeal (I.ideal ⟨⊤, isAffineOpen_top X⟩) := by
  conv_lhs => rw [← specIdeal_comap_toSpec I]
  rw [← Scheme.IdealSheafData.comap_comp]
  change (specIdeal _).comap (X.isoSpec.inv ≫ X.isoSpec.hom) = _
  rw [Iso.inv_hom_id, Scheme.IdealSheafData.comap_id]

end PiExponentSeshadri.IdealPullback

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TensorPure
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit,Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  rw [← Category.assoc,hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  have ha := a.comp_unit_app b P
  have hd := c.comp_unit_app d P
  let G : Y.Modules ⥤ PresheafOfModules Y.ringCatSheaf.obj :=
    SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let I : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  have hh := congrArg (fun h => h ≫ (I ⋙ G).map
    (((a.comp b).leftAdjointUniq (c.comp d)).hom.app P)) ha
  exact hh.symm.trans (he.trans hd)

end PiExponentSeshadri.TensorPure

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PushforwardTensor
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

def pullbackFrame (f : Y ⟶ X) {M : X.Modules} (e : M ≅ O X) :
    (Scheme.Modules.pullback f).obj M ≅ O Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

lemma pullbackUnit_adjunction (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end Geometry

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionPullback
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma pullback_endValue (f : Y ⟶ X) (a : O X ⟶ O X) :
    endValue ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom) = f.appTop (endValue a) := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let b := (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom
  have he : a ≫ u = u ≫ (Scheme.Modules.pushforward f).map b := by
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      a (pullbackUnitIso f).hom
    have hr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (pullbackUnitIso f).hom b
    rw [pullbackUnit_adjunction] at hn hr
    have hcomp : (pullbackUnitIso f).hom ≫ b =
        (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom := by simp [b]
    rw [hcomp] at hr
    exact hn.symm.trans hr
  have hev := congrArg (fun t : O X ⟶ (Scheme.Modules.pushforward f).obj (O Y) =>
      t.app ⊤ (1 : Γ(X,⊤))) he
  change f.app ⊤ (a.app ⊤ (1 : Γ(X,⊤))) = b.app (f ⁻¹ᵁ ⊤) (f.app ⊤ 1) at hev
  have hfOne : f.app ⊤ (1 : Γ(X,⊤)) = (1 : Γ(Y,f ⁻¹ᵁ ⊤)) := map_one (f.app ⊤).hom
  rw [hfOne] at hev
  exact hev.symm

lemma coefficient_pullback (f : Y ⟶ X) {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (pullbackFrame f e) (pullbackSection f s) =
      f.appTop (coefficient e s) := by
  unfold coefficient pullbackFrame pullbackSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  exact pullback_endValue f (s ≫ e.hom)

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_FramedPullback
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}

lemma endValue_conjugation (b : O Y ≅ O Y) (a : O Y ⟶ O Y) :
    endValue (b.hom ≫ a ≫ b.inv) = endValue a := by
  rw [endValue_comp, endValue_comp]
  have hb : endValue b.hom * endValue b.inv = 1 := by
    rw [← endValue_comp, b.hom_inv_id, endValue_id]
  calc
    endValue b.hom * (endValue a * endValue b.inv) =
      endValue a * (endValue b.hom * endValue b.inv) := by ring
    _ = endValue a := by rw [hb, mul_one]

lemma exists_frame_natIso (F G : X.Modules ⥤ Y.Modules) (v : F ≅ G)
    (uF : F.obj (O X) ≅ O Y) (uG : G.obj (O X) ≅ O Y)
    {M : X.Modules} (e : G.obj M ≅ O Y) (s : O X ⟶ M) :
    ∃ eF : F.obj M ≅ O Y,
      coefficient eF (uF.inv ≫ F.map s) = coefficient e (uG.inv ≫ G.map s) := by
  let b : O Y ≅ O Y := uF.symm ≪≫ v.app (O X) ≪≫ uG
  refine ⟨v.app M ≪≫ e ≪≫ b.symm, ?_⟩
  have h : (uF.inv ≫ F.map s) ≫ (v.app M).hom =
      b.hom ≫ (uG.inv ≫ G.map s) := by
    simp only [b, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    simp only [Iso.hom_inv_id_assoc]
    exact congrArg (fun q => uF.inv ≫ q) (v.hom.naturality s)
  change endValue (((uF.inv ≫ F.map s) ≫ (v.app M).hom) ≫ e.hom ≫ b.inv) = _
  rw [h]
  change endValue (b.hom ≫ (uG.inv ≫ G.map s ≫ e.hom) ≫ b.inv) = _
  exact endValue_conjugation b _

theorem exists_restricted_pullback_frame (f : Y ⟶ X) (U : X.Opens)
    {M : X.Modules} (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    ∃ eF : ((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι ≅
        O (f ⁻¹ᵁ U).toScheme,
      coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
        (f ∣_ U).appTop (coefficient e (restrictSection U.ι s)) := by
  let F : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
  let G : X.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U)
  let uF : F.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).mapIso (pullbackUnitIso f) ≪≫
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
  let uG : G.obj (O X) ≅ O (f ⁻¹ᵁ U).toScheme :=
    (Scheme.Modules.pullback (f ∣_ U)).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
      pullbackUnitIso (f ∣_ U)
  obtain ⟨eF,he⟩ := exists_frame_natIso F G (pullbackRestrictNatIso f U) uF uG
    (pullbackFrame (f ∣_ U) e) s
  refine ⟨eF, ?_⟩
  have he' : coefficient eF (restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s)) =
      coefficient (pullbackFrame (f ∣_ U) e)
        (pullbackSection (f ∣_ U) (restrictSection U.ι s)) := by
    let P : X.Modules ⥤ Y.Modules := Scheme.Modules.pullback f
    let R : Y.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι
    let S : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let Q : U.toScheme.Modules ⥤ (f ⁻¹ᵁ U).toScheme.Modules :=
      Scheme.Modules.pullback (f ∣_ U)
    let p : P.obj (O X) ≅ O Y := pullbackUnitIso f
    let r : R.obj (O Y) ≅ O (f ⁻¹ᵁ U).toScheme :=
      Scheme.Modules.restrictUnitIso (f ⁻¹ᵁ U).ι
    let a : S.obj (O X) ≅ O U.toScheme := Scheme.Modules.restrictUnitIso U.ι
    let q : Q.obj (O U.toScheme) ≅ O (f ⁻¹ᵁ U).toScheme := pullbackUnitIso (f ∣_ U)
    have hl : restrictSection (f ⁻¹ᵁ U).ι (pullbackSection f s) = uF.inv ≫ F.map s := by
      simp only [restrictSection, pullbackSection]
      change r.inv ≫ R.map (p.inv ≫ P.map s) = (r.inv ≫ R.map p.inv) ≫ R.map (P.map s)
      exact (congrArg (fun k => r.inv ≫ k) (R.map_comp p.inv (P.map s))).trans
        (Category.assoc r.inv (R.map p.inv) (R.map (P.map s))).symm
    have hr : pullbackSection (f ∣_ U) (restrictSection U.ι s) = uG.inv ≫ G.map s := by
      change q.inv ≫ Q.map (a.inv ≫ S.map s) = (q.inv ≫ Q.map a.inv) ≫ Q.map (S.map s)
      exact (congrArg (fun k => q.inv ≫ k) (Q.map_comp a.inv (S.map s))).trans
        (Category.assoc q.inv (Q.map a.inv) (Q.map (S.map s))).symm
    exact (congrArg (coefficient eF) hl).trans
      (he.trans (congrArg (coefficient (pullbackFrame (f ∣_ U) e)) hr).symm)
  rw [he', coefficient_pullback]

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_GlobalSectionClearing
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

instance instAddCommGroupCarrierOpenSections (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopCarrierOpenSections (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

end
end PiExponent.GlobalSectionClearing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_SectionDivision
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma section_value_naturality {M : X.Modules} (s : O X ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) =
      s.app V (1 : Γ(X,V)) := by
  have ht := CategoryTheory.congr_fun (s.mapPresheaf.naturality (homOfLE h).op)
    (1 : Γ(X,U))
  change s.app V (X.presheaf.map (homOfLE h).op (1 : Γ(X,U))) =
    M.presheaf.map (homOfLE h).op (s.app U (1 : Γ(X,U))) at ht
  simpa only [map_one] using ht.symm

lemma section_eq_zero_of_top_value {M : X.Modules} (s : O X ⟶ M)
    (hs : s.app ⊤ (1 : Γ(X,⊤)) = 0) : s = 0 := by
  ext U a
  change Γ(X,U) at a
  change s.app U a = 0
  have h := s.app_smul (r := a) (x := (1 : Γ(X,U)))
  change s.app U (a*1 : Γ(X,U)) = a • s.app U (1 : Γ(X,U)) at h
  rw [mul_one] at h
  rw [h, ← section_value_naturality s (show U ≤ ⊤ from le_top), hs,map_zero,smul_zero]

lemma section_eq_zero_of_local_restrictions {M : X.Modules} (s : O X ⟶ M)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ restrictSection U.ι s = 0) : s = 0 := by
  apply section_eq_zero_of_top_value
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  apply TopCat.Presheaf.section_ext F ⊤ (s.app ⊤ (1 : Γ(X,⊤))) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := hs x
  have hv : s.app U (1 : Γ(X,U)) = 0 := by
    have ht := congrArg (fun q : O U.toScheme ⟶ M.restrict U.ι =>
      q.app ⊤ (1 : Γ(U.toScheme,⊤))) hU
    change s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))) = 0 at ht
    rw [map_one] at ht
    have htop : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := by
      rw [Scheme.Hom.image_top_eq_opensRange,Scheme.Opens.opensRange_ι]
    suffices h : ∀ V : X.Opens, V = U → s.app V (1 : Γ(X,V)) = 0 →
        s.app U (1 : Γ(X,U)) = 0 from h _ htop ht
    intro V he ht
    subst V
    exact ht
  change M.presheaf.germ ⊤ x hx (s.app ⊤ (1 : Γ(X,⊤))) =
    M.presheaf.germ ⊤ x hx 0
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE (show U ≤ ⊤ from le_top)) x hxU]
  rw [section_value_naturality s, hv, map_zero, map_zero]

theorem global_division_of_local_lifts {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (s : O X ⟶ N)
    (hs : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ t : O U.toScheme ⟶ M.restrict U.ι,
        t ≫ (Scheme.Modules.restrictFunctor U.ι).map f = restrictSection U.ι s) :
    ∃! t : O X ⟶ M, t ≫ f = s := by
  have hz : s ≫ cokernel.π f = 0 := by
    apply section_eq_zero_of_local_restrictions
    intro x
    obtain ⟨U,hx,t,ht⟩ := hs x
    refine ⟨U,hx,?_⟩
    have hc : restrictSection U.ι (s ≫ cokernel.π f) =
        restrictSection U.ι s ≫ (Scheme.Modules.restrictFunctor U.ι).map (cokernel.π f) := by
      simp only [restrictSection]
      erw [Functor.map_comp, Category.assoc]
    rw [hc, ← ht, Category.assoc, ← Functor.map_comp,cokernel.condition,Functor.map_zero,comp_zero]
  refine ⟨Abelian.monoLift _ s hz,Abelian.monoLift_comp _ s hz,?_⟩
  intro t ht
  apply (cancel_mono f).mp
  rw [ht,Abelian.monoLift_comp]

lemma framed_local_division {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X)
    (f : M ⟶ N) (s : O X ⟶ N)
    (hs : coefficient d s ∈ Ideal.span {endValue (e.inv ≫ f ≫ d.hom)}) :
    ∃ t : O X ⟶ M, t ≫ f = s := by
  obtain ⟨r,hr⟩ := Ideal.mem_span_singleton.mp hs
  refine ⟨scalarEnd r ≫ e.inv,?_⟩
  apply (cancel_mono d.hom).mp
  apply endValue_injective
  rw [Category.assoc,Category.assoc,endValue_comp,endValue_scalarEnd]
  change r * endValue (e.inv ≫ f ≫ d.hom) = coefficient d s
  rw [mul_comm,← hr]

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCharts
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Projective

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open MvPolynomial
attribute [local instance] Classical.propDecidable
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R σ : Type*} [CommRing R] (i : σ)

lemma standardChart_isAffineOpen :
    IsAffineOpen (Proj.basicOpen (PolyGrade R σ) (X i)) :=
  Proj.isAffineOpen_basicOpen _ _ (poly_X_mem i) (by decide)

end PiExponentSeshadri.Projective

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_SurjectiveGradedMap
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open DirectSum HomogeneousLocalization
open scoped HomogeneousIdeal

variable {A B S T : Type*} [CommRing A] [CommRing B]
  [SetLike S A] [AddSubgroupClass S A] [SetLike T B] [AddSubgroupClass T B]
  {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]

theorem homogeneousAway_map_surjective (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
    {s : A} {d : ℕ} (hs : s ∈ 𝒜 d) : Function.Surjective (Away.map f s) := by
  intro x
  obtain ⟨n, y, hy, rfl⟩ := Away.mk_surjective _ (f.map_mem hs) x
  obtain ⟨p, hp, rfl⟩ := gradedMap_homogeneous_lift f hf hy
  exact ⟨Away.mk _ hs n p hp, Away.map_mk f s hs n p hp⟩

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationImmersion
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory
open scoped HomogeneousIdeal

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra


theorem projectiveMonomialMap_restrict (a : σ → ι →₀ ℕ) (s : σ) :
    projectiveMonomialMap (R := R) a ∣_ Proj.basicOpen (homogeneousSubmodule σ R) (X s) =
      (Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
        ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s))) ≫
          (Proj.basicOpenIsoSpec _ _ (isHomogeneous_X R s) (by decide)).inv := by
  let e := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  apply (cancel_epi e.inv).1
  apply (cancel_mono (Proj.basicOpen (homogeneousSubmodule σ R) (X s)).ι).1
  have h := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X s) (isHomogeneous_X R s)
  simp only [Category.assoc, e, Iso.inv_hom_id_assoc]
  erw [Category.assoc, morphismRestrict_ι]
  simpa only [Proj.awayι, Category.assoc, projectiveMonomialMap,
    Proj.map_preimage_basicOpen] using h

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_PolynomialProjectiveStructure
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable (R σ : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

instance polynomialProjectiveProjection_proper [Finite σ] :
    IsProper (polynomialProjectiveProjection R σ) := by
  have : IsProper (Proj.toSpecZero (homogeneousSubmodule σ R)) := inferInstance
  have : IsIso (Spec.map (CommRingCat.ofHom (polynomialGradeZeroEquiv R σ).toRingHom)) := by
    change IsIso (Spec.map (polynomialGradeZeroEquiv R σ).toCommRingCatIso.hom)
    infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ inferInstance inferInstance

end PiExponent

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_WeightedProjectiveStructure
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory

universe u
variable {R ι σ : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def projection (a : σ → ι →₀ ℕ) :
    Proj (imageGrade (R := R) a) ⟶ Spec (CommRingCat.of R) :=
  projectiveMonomialMap a ≫ polynomialProjectiveProjection R σ

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationGeometry
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open MvPolynomial AlgebraicGeometry CategoryTheory Topology

universe u
variable {R ι σ : Type u} [CommRing R]

instance affineChartMap_isOpenImmersion (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    IsOpenImmersion (affineChartMap (R := R) a z hz coordinate hcoordinate) := by
  let e := constantProjectiveChartIso (R := R) a z hz coordinate hcoordinate
  have : IsOpenImmersion e.inv := inferInstance
  exact IsOpenImmersion.comp _ _

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedAffineParametrization
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.WeightedCompactification

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open PiExponentSeshadri.Projective

universe u
variable {R ι σ : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem imageEvaluation_gradedImageMap (a : σ → ι →₀ ℕ) (p : MvPolynomial σ R) :
    imageEvaluation (R := R) a (gradedImageMap (R := R) a p) = affineMonomialMap (R := R) a p := by
  have h : (imageEvaluation (R := R) a).comp (gradedImageMap (R := R) a).toRingHom =
      affineMonomialMap (R := R) a := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_C]
      change (eval₂Hom (RingHom.id (MvPolynomial ι R)) (fun _ : Unit => 1))
        (homogeneousMonomialMap a (C r)) = C r
      simp [homogeneousMonomialMap]
    · intro s
      simp only [RingHom.comp_apply, affineMonomialMap, eval₂Hom_X']
      change imageEvaluation (R := R) a (imageCoordinate (R := R) a s) = monomial (a s) 1
      exact imageEvaluation_coordinate a s
  exact RingHom.congr_fun h p

theorem chartEvaluation_comp_awayMap (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0) :
    (chartEvaluation (R := R) a z hz).comp (Away.map (gradedImageMap (R := R) a) (X z)) =
      evalAway (affineMonomialMap (R := R) a) (X z)
        (by simp [affineMonomialMap, hz]) := by
  apply RingHom.ext
  intro q
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (PolyGrade R σ) (poly_X_mem z) q
  change chartEvaluation (R := R) a z hz
    (Away.map (gradedImageMap (R := R) a) (X z) (Away.mk _ (poly_X_mem z) n p hp)) = _
  rw [Away.map_mk (gradedImageMap (R := R) a) (X z) (poly_X_mem z) n p hp]
  erw [chartEvaluation_mk]
  rw [imageEvaluation_gradedImageMap]
  have h := evalAway_mk_clear (affineMonomialMap (R := R) a) (poly_X_mem z)
    (show IsUnit (affineMonomialMap (R := R) a (X z)) from by
      simp [affineMonomialMap, hz]) n p hp
  simpa [affineMonomialMap, hz] using h.symm


end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Cohomology_PencilCohomologySections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ModuleFlasque
variable {X : Scheme.{0}}

instance instAddCommGroupCarrierOpenSections (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveProductFormula
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CurveProductFormula
open PiExponent.CurveZeroPole PiExponent.CurveValuationCenter
open PiExponent.WeightedCurveDegree

theorem order_ne_zero_iff_positive_or_inverse
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) (z : Eˣ) :
    placeOrder p z ≠ 0 ↔ 0 < p.valuation (z : E) ∨ 0 < p.valuation ((z : E)⁻¹) := by
  rw [valuation_pos_iff_order_pos p z]
  rw [← Units.val_inv_eq_inv_val]
  rw [valuation_pos_iff_order_pos, placeOrder_inv]
  omega

theorem finite_support_placeOrder
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] :
    (Function.support (fun p : NormalizedPlace F E => placeOrder p (Units.mk0 f hf.ne_zero))).Finite := by
  let : FiniteDimensional (IntermediateField.adjoin F {f⁻¹}) E :=
    (adjoin_inverse_eq (F := F) f).symm ▸ inferInstance
  apply ((finite_positivePlaces f hf).union
    (finite_positivePlaces f⁻¹ (transcendental_inverse f hf))).subset
  intro p hp
  exact (order_ne_zero_iff_positive_or_inverse p (Units.mk0 f hf.ne_zero)).mp hp

def principalDivisor
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] : NormalizedPlace F E →₀ ℤ :=
  Finsupp.ofSupportFinite (fun p => placeOrder p (Units.mk0 f hf.ne_zero))
    (finite_support_placeOrder f hf)

@[simp] theorem principalDivisor_apply
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E] (p : NormalizedPlace F E) :
    principalDivisor f hf p = placeOrder p (Units.mk0 f hf.ne_zero) := rfl

end PiExponent.CurveProductFormula

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_AdmissibleCurveInequality
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.AdmissibleParameters

variable {nu Lambda C : ℝ} (d : AdmissibleParameters nu Lambda C)

def curveCenters : Fin d.K → Fin d.m → ℂ :=
  fun j i => (j.val : ℂ) *
    MatrixArithmetic.rationalCenters (fun i : Fin d.m => d.p i.val)
      (fun i : Fin d.m => d.q i.val) i

end PiExponent.AdmissibleParameters
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_LineBundleGluingSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.LineBundleGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}} {ι : Type} {U : ι → X.Opens} (c : Cocycle U)

lemma openFrame_unit (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    (modulePresheafRestrict W.ι).map
        ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)) ≫
      (openFrame c i W hW).hom.val = (openPresheafFrame c i W hW).hom := by
  simp only [openFrame]
  let R := modulePresheafRestrict W.ι
  let F : PresheafOfModules W.toScheme.ringCatSheaf.obj ⥤ W.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 W.toScheme.ringCatSheaf.obj)
  let a : (sheaf c).restrict W.ι ⟶ F.obj (R.obj (presheaf c)) :=
    (moduleSheafificationRestrict W.ι).hom.app (presheaf c)
  let b : F.obj (O W.toScheme).val ⟶ O W.toScheme :=
    (TensorPure.adj W.toScheme).counit.app (O W.toScheme)
  let e := (openPresheafFrame c i W hW).hom
  change R.map ((TensorPure.adj X).unit.app (presheaf c)) ≫
    a.val ≫ (F.map e).val ≫ b.val = e
  have h := TensorPure.sheafify_restrict_unit W.ι (presheaf c)
  have h₁ := Category.assoc
    (R.map ((TensorPure.adj X).unit.app (presheaf c))) a.val ((F.map e).val ≫ b.val)
  have h₂ := congrArg (fun q => q ≫ (F.map e).val ≫ b.val) h
  have h₃ := sheafification_unit_counit_map W.toScheme _ (O W.toScheme) e
  exact h₁.symm.trans (h₂.trans h₃)

lemma openFrame_unit_apply (i : ι) (W : X.Opens) (hW : W ≤ U i)
    (V : W.toScheme.Opens) (s : sections c (W.ι ''ᵁ V)) :
    (openFrame c i W hW).hom.app V
      ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op (W.ι ''ᵁ V))) s) =
      s.val ⟨i,W.ι ''ᵁ V,le_rfl,(W.ι_image_le V).trans hW⟩ := by
  have h := congrArg (fun q => q.app (op V) s) (openFrame_unit c i W hW)
  exact h

lemma globalSection_app_one (s : sections c ⊤) (V : X.Opens) :
    (globalSection c s).app V (1 : Γ(X,V)) =
      (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
        (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op V)
          (restrict c le_top s)) := by
  have ht := (moduleSectionEquiv (sheaf c)).apply_symm_apply
    ((((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c)).app (op ⊤)) s)
  change (globalSection c s).app ⊤ (1 : Γ(X,⊤)) = _ at ht
  rw [← section_value_natural (globalSection c s) (homOfLE (show V ≤ ⊤ from le_top)), ht]
  exact (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).unit.app (presheaf c))
        (homOfLE (show V ≤ ⊤ from le_top)).op s).symm

theorem globalSection_coefficient (s : sections c ⊤) (i : ι)
    (W : X.Opens) (hW : W ≤ U i) :
    W.topIso.hom (coefficient (openFrame c i W hW)
      (restrictSection W.ι (globalSection c s))) = s.val ⟨i,W,le_top,hW⟩ := by
  change W.topIso.hom ((openFrame c i W hW).hom.app ⊤
    ((globalSection c s).app (W.ι ''ᵁ ⊤)
      ((W.ι.appIso ⊤).inv (1 : Γ(W.toScheme,⊤))))) = _
  rw [map_one, globalSection_app_one, openFrame_unit_apply]
  change W.topIso.hom (s.val ⟨i,W.ι ''ᵁ ⊤,le_top,(W.ι_image_le ⊤).trans hW⟩) = _
  rw [← s.property.1 i W (W.ι ''ᵁ ⊤) le_top hW (W.ι_image_le ⊤)]
  simp only [Scheme.Opens.topIso_hom]
  change (X.presheaf.map _ ≫ X.presheaf.map _) (s.val ⟨i,W,le_top,hW⟩) = _
  erw [← Functor.map_comp]
  change X.presheaf.map (𝟙 (op W)) (s.val ⟨i,W,le_top,hW⟩) = _
  exact congrArg (fun q => q (s.val ⟨i,W,le_top,hW⟩)) (X.presheaf.map_id (op W))

end
end PiExponentSeshadri.LineBundleGluing

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveCoordinateValues
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

lemma evalAway_coordinate {R : Type} [CommRing R]
    (k : K →+* R) (a : σ → R) (hi : a i = 1) (j : σ) :
    evalAway (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
      (chartCoordinate (R := K) i j) = a j := by
  have h := evalAway_mk_clear (eval₂Hom k a) (poly_X_mem (R := K) i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    1 (X j) (by simpa using poly_X_mem (R := K) j)
  simpa only [chartCoordinate, eval₂Hom_X', hi, one_pow, mul_one] using h

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_ProjectiveEmbeddingCharts
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace Projective

section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open scoped AlgebraicGeometry
variable {K σ : Type u} [CommRing K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma evalAway_constants_comp {R : Type u} [CommRing R] (k : K →+* R) (a : σ → R)
    (i : σ) (hi : a i = 1) :
    (evalAway (𝒜 := homogeneousSubmodule σ K) (eval₂Hom k a) (X i)
      (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))).comp
      ((fromZeroRingHom (homogeneousSubmodule σ K) (.powers (X i))).comp
        projectiveConstants) = k := by
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (HomogeneousLocalization.fromZeroRingHom (homogeneousSubmodule σ K)
      (.powers (X i)) (projectiveConstants c)).val = k c
  change IsLocalization.Away.lift (X i)
    (by simpa only [eval₂Hom_X', hi] using (isUnit_one : IsUnit (1 : R)))
    (algebraMap (MvPolynomial σ K) (Localization.Away (X i)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

end

open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
attribute [local instance] MvPolynomial.gradedAlgebra

end Projective

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_AlgebraicJetPackets
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [CommRing R] {m : ℕ}

theorem triangularMap_comp_inverse (c : Fin m → R) (G : Fin m → Polynomial R) :
    (triangularMap c G).comp (inverseTriangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      triangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, triangularMap_X_zero, map_one, AlgHom.id_apply]
    rw [show (1 + X (0 : Fin (m+1)) - 1 : MvPolynomial (Fin (m+1)) R) = X 0 by ring]
    ring

theorem inverseTriangularMap_comp (c : Fin m → R) (G : Fin m → Polynomial R) :
    (inverseTriangularMap c G).comp (triangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, triangularMap_X_succ, map_add,
      inverseTriangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, inverseTriangularMap_X_zero, AlgHom.id_apply]
    ring

def triangularEquiv (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R ≃ₐ[R] MvPolynomial (Fin (m+1)) R :=
  AlgEquiv.ofAlgHom (triangularMap c G) (inverseTriangularMap c G)
    (triangularMap_comp_inverse c G) (inverseTriangularMap_comp c G)

end PiExponent.AlgebraicJetPackets

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace PiExponent.CompactJetIdeal

universe u
variable {U X S : Scheme.{u}}

theorem support_extend {J : Type*} [Finite J]
    (I : U.IdealSheafData) (j : U ⟶ X) [QuasiCompact j]
    (π : X ⟶ S) [IsSeparated π]
    (p : J → (S ⟶ U)) (hp : ∀ a, (p a ≫ j) ≫ π = 𝟙 S)
    (hsupport : (I.support : Set U) = ⋃ a, Set.range (p a)) :
    ((extend I j).support : Set X) = j '' (I.support : Set U) := by
  change ((I.map j).support : Set X) = _
  rw [Scheme.IdealSheafData.support_map]
  exact (image_support_isClosed I j π p hp hsupport).closure_eq

end PiExponent.CompactJetIdeal
end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactJetPolynomial
attribute [-instance] _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponent.CompactJetPolynomial

open MvPolynomial AlgebraicJetPackets
open scoped BigOperators

variable {k : Type*} [Field k] {m : ℕ}

theorem eval_center_inverse (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    (MvPolynomial.aeval (center c)).comp (inverseTriangularMap c G) =
      MvPolynomial.aeval (0 : Fin (m+1) → k) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [center]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, ← Polynomial.aeval_algHom_apply]
    simp [center, Polynomial.coe_aeval_eq_eval, hG i]

theorem span_coordinates (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    Ideal.span (Set.range (coordinates c G)) = WeightedBezout.pointIdeal (center c) := by
  let φ := (inverseTriangularMap c G).toRingHom
  have hs : Function.Surjective φ := (triangularEquiv c G).symm.surjective
  have hc : (WeightedBezout.pointIdeal (center c)).comap φ =
      WeightedBezout.pointIdeal (0 : Fin (m+1) → k) := by
    ext P
    change MvPolynomial.aeval (center c) (inverseTriangularMap c G P) = 0 ↔
      MvPolynomial.aeval (0 : Fin (m+1) → k) P = 0
    rw [← AlgHom.comp_apply, eval_center_inverse c G hG]
  calc
    Ideal.span (Set.range (coordinates c G)) =
        (Ideal.span (Set.range (X (R := k) : Fin (m+1) → _))).map φ := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = (WeightedBezout.pointIdeal (0 : Fin (m+1) → k)).map φ := by
      congr 1
      rw [WeightedBezout.pointIdeal_eq_span]
      simp
    _ = WeightedBezout.pointIdeal (center c) := by
      rw [← hc, Ideal.map_comap_of_surjective φ hs]

theorem radical_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal c G e).radical = WeightedBezout.pointIdeal (center c) := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal (center c)).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hz : coordinates c G i ∈ WeightedBezout.pointIdeal (center c) := by
      rw [← span_coordinates c G hG]
      exact Ideal.subset_span ⟨i,rfl⟩
    change MvPolynomial.aeval (center c) (coordinates c G i ^ e i) = 0
    rw [map_pow, (WeightedBezout.mem_pointIdeal _ _).mp hz, zero_pow (he i).ne']
  · rw [← span_coordinates c G hG]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i,rfl⟩⟩

theorem zeroLocus_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdeal c G e : Set _) = {centerPoint c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal c G hG e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem zeroLocus_finset_prod_powerIdeal {J : Type*} (s : Finset J)
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j ∈ s, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      (fun j => centerPoint (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdeal (c j) G hG e he, ih]
    rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq]

theorem zeroLocus_prod_powerIdeal {J : Type*} [Fintype J]
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      Set.range (fun j => centerPoint (c j)) := by
  simpa using zeroLocus_finset_prod_powerIdeal Finset.univ c G hG e he

end PiExponent.CompactJetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Jets_CompactLogJetIdeal
attribute [-instance] _root_.OAI.PiExponent.SeparablePointLength.point_liesOver _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped BigOperators
namespace PiExponent.CompactLogJetIdeal
open CompactJetPolynomial

variable {m : ℕ}

def structureMap (m : ℕ) : affineSpace m ⟶ base :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)))

def point (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom)

theorem point_section (c : Fin m → ℂ) : point c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (center c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (c : Fin m → ℂ) : Set.range (point c) = {centerPoint c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (center c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (center c))

theorem support_specIdeal {R : Type} [CommRing R] (I : Ideal R) :
    ((PiExponentSeshadri.IdealPullback.specIdeal I).support : Set (Spec (CommRingCat.of R))) =
      PrimeSpectrum.zeroLocus (I : Set R) := by
  rw [PiExponentSeshadri.IdealPullback.specIdeal,
    Scheme.IdealSheafData.coe_support_ofIdealTop, Spec_zeroLocus, ← Ideal.coe_comap]
  rw [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv)]

theorem support_affineIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal c T e).support : Set (affineSpace m)) =
      ⋃ a, Set.range (point (c a)) := by
  rw [affineIdeal, support_specIdeal]
  unfold polynomialIdeal
  rw [zeroLocus_prod_powerIdeal c (logPolynomials T) (logPolynomials_eval_zero T) e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
    exact ⟨a, (Set.mem_singleton_iff.mp ha).symm⟩

theorem support_compactIdeal {J : Type*} [Fintype J] (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal c T e j).support : Set X) =
      ⋃ a, Set.range (point (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal c T e) j π
    (fun a => point (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal c T e he),
    support_affineIdeal c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

end PiExponent.CompactLogJetIdeal
end

end OAI
end


