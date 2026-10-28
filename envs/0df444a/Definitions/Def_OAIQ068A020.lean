-- Prove2me | Definitions.Def_OAIQ068A020
-- name    : OAIQ068A020
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T07:53:10.35277+00:00
-- url     : https://prove2.me/theorems/2f70a003-b67f-46de-95fd-869bd1d04469
-- title:
--   Definitions bundle OAIQ068A020 of the split of OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 109 declarations of OpenAI's Lean: 40 definitions, 8 instances and 61 theorems. The definitions and types are `OAI.PiExponent.AdmissibleBlowupGeometry.A`, `OAI.PiExponent.AdmissibleBlowupGeometry.J`, `OAI.PiExponent.AdmissibleBlowupGeometry.blowup`, `OAI.PiExponent.AdmissibleBlowupGeometry.centerIdeal`, `OAI.PiExponent.AdmissibleBlowupGeometry.compactificationStructureMap`, `OAI.PiExponent.AdmissibleBlowupGeometry.hyperplane`, `OAI.PiExponent.AdmissibleBlowupGeometry.logCutoff`, `OAI.PiExponent.AdmissibleBlowupGeometry.origin`, `OAI.PiExponent.AdmissibleBlowupGeometry.projection`, `OAI.PiExponentSeshadri.AffineBlowup.projection`, `OAI.PiExponentSeshadri.AffineBlowup.scheme`, `OAI.PiExponentSeshadri.BlowupGluing.affineRestrictionIso`, `OAI.PiExponentSeshadri.BlowupGluing.cover`, `OAI.PiExponentSeshadri.BlowupGluing.diagram`, `OAI.PiExponentSeshadri.BlowupGluing.diagramMap`, `OAI.PiExponentSeshadri.BlowupGluing.exceptionalLineBundle`, `OAI.PiExponentSeshadri.BlowupGluing.gluing`, `OAI.PiExponentSeshadri.BlowupGluing.localProjection`, `OAI.PiExponentSeshadri.BlowupGluing.localScheme`, `OAI.PiExponentSeshadri.BlowupGluing.projection`, `OAI.PiExponentSeshadri.BlowupGluing.scheme`, `OAI.PiExponentSeshadri.BlowupGluing.transition`, `OAI.PiExponentSeshadri.Geometry.IsBlowup`, `OAI.PiExponentSeshadri.Geometry.IsBlowup.iso`, `OAI.PiExponentSeshadri.Geometry.idealLineBundle`, `OAI.PiExponentSeshadri.Geometry.lineBundleOfCover`, `OAI.PiExponentSeshadri.Geometry.lineTensorAssoc`, `OAI.PiExponentSeshadri.Geometry.moduleSectionMultiplyRight`, `OAI.PiExponentSeshadri.Geometry.moduleTensorRestrictFrame`, `OAI.PiExponentSeshadri.Geometry.moduleTwistForward`, `OAI.PiExponentSeshadri.Geometry.moduleTwistRestrictFrame`, `OAI.PiExponentSeshadri.Geometry.moduleTwistSection`, `OAI.PiExponentSeshadri.Geometry.moduleTwistStep`, `OAI.PiExponentSeshadri.Geometry.sheafificationTensorLeft`, `OAI.PiExponentSeshadri.InvertibleLocal.frameOfLE`, `OAI.PiExponentSeshadri.InvertibleLocal.restrictLineBundle`, `OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion`, `OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion`, `OAI.PiExponentSeshadri.ReesGrading.exceptionalLineBundle`, `OAI.PiExponentSeshadri.ReesGrading.principalScheme`.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PiExponent_Ampleness_AdmissibleBlowupGeometry`, `PiExponent_Ampleness_AffineBlowupUniversal`, `PiExponent_Ampleness_BlowupIdeal`, `PiExponent_Ampleness_BlowupUniversalBaseChange`, `PiExponent_Ampleness_GlobalBlowupGluing`, `PiExponent_Ampleness_GlobalBlowupRestriction`, `PiExponent_Ampleness_ReesExceptional`, `PiExponent_Ampleness_ReesPrincipalLift`, `PiExponent_Ampleness_ReesUniversalUniqueness`, `PiExponent_Approximation_CoherentTwistPresentation`, `PiExponent_Approximation_LinePowerLaws`, `PiExponent_Approximation_PowerSectionExtension`, `PiExponent_Approximation_TwistSections`, `PiExponent_Approximation_WeightedAffineParametrization`, `PiExponent_Approximation_WeightedCompactificationImmersion`, `PiExponent_Geometry_CurveMonomialMap`, `PiExponent_LocalAlgebra_GlobalInvertibleIdeal`, `PiExponent_LocalAlgebra_InvertibleIdealLocal`.
--
--   **Imports.** It imports the bundles `OAIQ068A012` and `OAIQ068A013` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ068A028`, `OAIQ068A029`, `OAIQ068A030`, `OAIQ068A031`, `OAIQ068A032` and `OAIQ068A033`.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit 1581d4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A012
import Definitions.Def_OAIQ068A013

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

namespace Geometry
open CategoryTheory AlgebraicGeometry

def IsBlowup {X B : Scheme} (I : X.IdealSheafData) (π : B ⟶ X) : Prop :=
  InvertiblePullbackIdeal I π ∧ ∀ (Y : Scheme) (f : Y ⟶ X),
    InvertiblePullbackIdeal I f → ∃! h : Y ⟶ B, h ≫ π = f

end Geometry

namespace InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}
lemma invertible_of_local_equations
    (hf : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      obtain ⟨U, hyU, r, hr, hIr⟩ := hf y
      exact ⟨U.1, hyU, IdealModule.frame_restriction (I.comap f) U.1.ι r hIr hr.1⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry

end InvertibleLocal

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_ReesExceptional
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry
open CategoryTheory AlgebraicGeometry

def lineBundleOfCover {X : Scheme} (M : X.Modules) (C : X.OpenCover)
    (h : ∀ i, Nonempty (M.restrict (C.f i) ≅ IdealModule.unit (C.X i))) : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    refine ⟨(C.f (C.idx x)).opensRange, C.covers x, ?_⟩
    exact ⟨IdealModule.frameOnRange M (C.f (C.idx x)) (h (C.idx x)).some⟩

def idealLineBundle {X : Scheme} (I : X.IdealSheafData) (C : X.AffineOpenCover)
    (r : ∀ i, Γ(Spec (C.X i), ⊤))
    (h : ∀ i, (I.comap (C.f i)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r i})
    (hr : ∀ i, IsLeftRegular (r i)) : LineBundle X :=
  lineBundleOfCover (IdealModule.closedModule I) C.openCover
    (fun i => by
      let : IsOpenImmersion (C.f i) := C.map_prop i
      exact IdealModule.frame_restriction I (C.f i) (r i) (h i) (hr i))

end PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.ReesGrading

open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

def exceptionalLineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ IdealModule.unit (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance exceptionalInclusion_mono : Mono (exceptionalInclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))



lemma exceptional_presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) := by
  refine ⟨exceptionalInclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem exceptional_invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I)
    (projection I) :=
  ⟨exceptionalLineBundle I, exceptionalInclusion I, exceptional_presents I⟩

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

namespace PiExponentSeshadri.ReesGrading

open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (X : Scheme.{u}) (f : R →+* Γ(X, ⊤)) (r : Γ(X, ⊤))
variable (hI : I.map f = Ideal.span {r}) (hr : IsRegular r)

def principalScheme : X ⟶ affineBlowup I :=
  Proj.fromOfGlobalSections (piece I) (principalMap I f r hI hr)
    (principalMap_irrelevant I f r hI hr)

@[reassoc]
lemma principalScheme_projection :
    principalScheme I X f r hI hr ≫ projection I =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) := by
  let g : CommRingCat.of (piece I 0) ⟶ Γ(X, ⊤) :=
    CommRingCat.ofHom ((principalMap I f r hI hr).comp (algebraMap _ _))
  have hg : (zeroIso I).hom ≫ g = CommRingCat.ofHom f := by
    ext s
    exact principalMap_base I f r hI hr s
  have h : principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I) =
      X.toSpecΓ ≫ Spec.map g :=
    Proj.fromOfGlobalSections_toSpecZero (piece I) (principalMap I f r hI hr)
      (principalMap_irrelevant I f r hI hr)
  change principalScheme I X f r hI hr ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  calc
    _ = (principalScheme I X f r hI hr ≫ Proj.toSpecZero (piece I)) ≫
        Spec.map (zeroIso I).hom := (Category.assoc _ _ _).symm
    _ = (X.toSpecΓ ≫ Spec.map g) ≫ Spec.map (zeroIso I).hom :=
      congrArg (fun q : X ⟶ Spec (CommRingCat.of (piece I 0)) =>
        q ≫ Spec.map (zeroIso I).hom) h
    _ = X.toSpecΓ ≫ Spec.map ((zeroIso I).hom ≫ g) := by
      rw [Category.assoc, Spec.map_comp]
    _ = _ := congrArg (fun q : CommRingCat.of R ⟶ Γ(X, ⊤) =>
      X.toSpecΓ ≫ Spec.map q) hg

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
open Polynomial CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

instance projection_separated : IsSeparated (projection I) := by
  have hP : IsSeparated (Proj.toSpecZero (piece I)) := inferInstance
  have hQ : IsSeparated (Spec.map (zeroIso I).hom) := inferInstance
  exact MorphismProperty.comp_mem (@IsSeparated) _ _ hP hQ

lemma projection_mem (x : affineBlowup I) (s : R) :
    s ∈ ((projection I) x).asIdeal ↔
      algebraMap R (reesAlgebra I) s ∈ x.asHomogeneousIdeal := by
  change zeroEquiv I s ∈ ((Proj.toSpecZero (piece I)) x).asIdeal ↔ _
  exact ProjBase.toSpecZero_mem (piece I) x (zeroEquiv I s)

lemma projection_preimage (s : R) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen s =
      Proj.basicOpen (piece I) (algebraMap R (reesAlgebra I) s) := by
  ext x
  exact not_congr (projection_mem I x s)

lemma projection_preimage_le_chart (a : I) :
    projection I ⁻¹ᵁ PrimeSpectrum.basicOpen a.val ≤
      Proj.basicOpen (piece I) (generator I a) := by
  rw [projection_preimage]
  intro x hx
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))
  have h : x ∈ Proj.basicOpen (piece I)
      (algebraMap R (reesAlgebra I) a.val * generator I b) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hx, hb⟩
  rw [base_generator_comm, Proj.basicOpen_mul] at h
  exact h.2

open SpecMaps

lemma ext_of_unit_generator {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hu : IsUnit (coordinate f a.val)) : g = h := by
  let hOpen : IsOpenImmersion ((chartCover I).f a) := (chartCover I).map_prop a
  have ht : f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val = ⊤ := by
    rw [preimage_basicOpen, Scheme.basicOpen_of_isUnit _ hu]
  have hrange (k : Y ⟶ affineBlowup I) (hk : k ≫ projection I = f) :
      Set.range k ⊆ Set.range ((chartCover I).f a) := by
    rintro _ ⟨y, rfl⟩
    change k y ∈ ((chartCover I).f a).opensRange
    change k y ∈ (Proj.awayι (piece I) (generator I a) (generator_mem I a)
      (show 0 < (1 : ℕ) from Nat.zero_lt_one)).opensRange
    rw [Proj.opensRange_awayι]
    apply projection_preimage_le_chart I a
    change (projection I) (k y) ∈ PrimeSpectrum.basicOpen a.val
    rw [← Scheme.Hom.comp_apply, hk]
    exact ht.ge (Set.mem_univ y)
  let g' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  let h' : Y ⟶ Spec (CommRingCat.of (chart I a)) := @IsOpenImmersion.lift _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have hg' : g' ≫ (chartCover I).f a = g :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) g hOpen (hrange g hg)
  have hh' : h' ≫ (chartCover I).f a = h :=
    @IsOpenImmersion.lift_fac _ _ _ ((chartCover I).f a) h hOpen (hrange h hh)
  have eg : g' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      g' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hg').trans hg))
  have eh : h' ≫ Spec.map (CommRingCat.ofHom (chartBase I a)) = f := by
    exact (congrArg (fun q : Spec (CommRingCat.of (chart I a)) ⟶ Spec (CommRingCat.of R) =>
      h' ≫ q) (chartCover_projection I a).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q : Y ⟶ affineBlowup I => q ≫ projection I) hh').trans hh))
  have he : coordinate g' (chartBase I a a.val) = coordinate f a.val := by
    have hc := congrArg coordinate eg
    rw [coordinate_comp_spec] at hc
    exact ConcreteCategory.congr_hom hc a.val
  have hgh := chart_scheme_ext I a g' h' (eg.trans eh.symm) (by rw [he]; exact hu.isRegular)
  rw [← hg', ← hh', hgh]


lemma ext_on_generator_open {Y : Scheme.{u}} (a : I)
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) :
    (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ g =
      (f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val).ι ≫ h := by
  let U : Y.Opens := f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val
  apply ext_of_unit_generator I a _ _ (U.ι ≫ f)
  · rw [Category.assoc, hg]
  · rw [Category.assoc, hh]
  · apply isUnit_coordinate_of_preimage_top
    erw [Scheme.Hom.comp_preimage]
    exact U.ι_preimage_self

lemma ext_of_unit_ideal {Y : Scheme.{u}}
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hI : I.map (coordinate f).hom = ⊤) : g = h := by
  refine Scheme.hom_ext_of_forall g h ?_
  intro y
  have ha : ∃ a : I, y ∈ f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val :=
    ideal_unit_generator (R := CommRingCat.of R) I f hI y
  obtain ⟨a, hay⟩ := ha
  refine ⟨f ⁻¹ᵁ PrimeSpectrum.basicOpen a.val, hay, ?_⟩
  exact ext_on_generator_open I a g h f hg hh

lemma principal_unique {Y : Scheme.{u}} [IsAffine Y]
    (g h : Y ⟶ affineBlowup I) (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (r : Γ(Y, ⊤)) (hI : I.map (coordinate f).hom = Ideal.span {r}) (hr : IsRegular r) :
    g = h := by
  apply SchematicExt.ext_of_ker_eq_bot_of_isSeparated (projection I) (hg.trans hh.symm)
    (Y.basicOpen r).ι (SchematicExt.basicOpen_ker_eq_bot r hr)
  exact ext_of_unit_ideal I _ _ ((Y.basicOpen r).ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh])
    (principal_basicOpen_unit_ideal I f r hI)

end PiExponentSeshadri.ReesGrading

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_CoherentTwistPresentation
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
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

def moduleTensorRestrictFrame (U : X.Opens) (L : X.Modules)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    moduleTensorRightFunctor L ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι :=
  NatIso.ofComponents
    (fun M => moduleTensorRestrict U M L ≪≫ moduleTensorFrame (M.restrict U.ι) e)
    (by
      intro M N f
      change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (𝟙 L)) ≫
          ((moduleTensorRestrict U N L).hom ≫ (moduleTensorFrame (N.restrict U.ι) e).hom) =
        ((moduleTensorRestrict U M L).hom ≫ (moduleTensorFrame (M.restrict U.ι) e).hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map f
      rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
        CategoryTheory.Functor.map_id, moduleTensorFrame_natural, Category.assoc])

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_PowerSectionExtension
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace InvertibleLocal
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

def frameOfLE (M : Y.Modules) {U V : Y.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    M.restrict V.ι ≅ structureSheaf V.toScheme := by
  let e' := (Scheme.Modules.restrictFunctorComp (Y.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (Y.homOfLE h)).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso (Y.homOfLE h)
  simp only [Y.homOfLE_ι h] at e'
  exact e'

lemma affine_frame (J : LineBundle Y) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
  exact ⟨⟨U, hU⟩, hyU, ⟨frameOfLE J.sheaf hUV e⟩⟩

end InvertibleLocal

end PiExponentSeshadri

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_InvertibleIdealLocal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PiExponentSeshadri.InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
universe u
variable {X Y Z : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)

lemma image_eq_comap [IsAffine X] (h : PresentsPullbackIdeal I f J ι) (U : Y.affineOpens) :
    sectionImageIdeal J ι U.1 = (I.comap f).ideal U := by
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have e : U.1 ≤ f ⁻¹ᵁ V.1 := by simp [V]
  exact (h.2 U V e).trans (IdealPullback.comap_ideal I f U V e).symm

variable {I f}

def restrictedInclusion (j : Z ⟶ Y) [IsOpenImmersion j] :
    J.sheaf.restrict j ⟶ structureSheaf Z :=
  (Scheme.Modules.restrictFunctor j).map ι ≫ (Scheme.Modules.restrictUnitIso j).hom

instance restrictedInclusion_mono (j : Z ⟶ Y) [IsOpenImmersion j] [Mono ι] :
    Mono (restrictedInclusion J ι j) := by
  exact mono_comp_iso ((Scheme.Modules.restrictFunctor j).map ι)
    (Scheme.Modules.restrictUnitIso j)

lemma restricted_image [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  ext r
  change Γ(Z, U.1) at r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← image_eq_comap I f J ι h
    ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩]
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) => k (ι.val.app (op (j ''ᵁ U.1)) s))
      (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation [IsAffine X] (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] [IsAffine Z]
    (e : J.sheaf.restrict j ≅ structureSheaf Z) :
    ∃ r : Γ(Z, ⊤), IsRegular r ∧
      ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top Z⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit Z ⟶ UnitEndomorphism.unit Z :=
    e.inv ≫ restrictedInclusion J ι j
  let : Mono (restrictedInclusion J ι j) := restrictedInclusion_mono J ι j
  have : Mono g := mono_iso_inv_comp_p1 e (restrictedInclusion J ι j)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤, ← restricted_image J ι h j ⟨⊤, isAffineOpen_top Z⟩]
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι j).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict j ⟶ J.sheaf.restrict j => k.val.app (op ⊤) s)
        e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

end

section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y : Scheme}

lemma affine_local_equation [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
        Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨U, hyU, ⟨e⟩⟩ := affine_frame J y
  refine ⟨U, hyU, ?_⟩
  exact local_equation J ι h U.1.ι e

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme}


def restrictLineBundle (J : LineBundle Y) (j : Z ⟶ Y) [IsOpenImmersion j] : LineBundle Z where
  sheaf := J.sheaf.restrict j
  locallyRankOne z := by
    obtain ⟨U, hzU, ⟨e⟩⟩ := J.locallyRankOne (j z)
    let V := j ⁻¹ᵁ U
    refine ⟨V, hzU, ⟨?_⟩⟩
    let e' := (Scheme.Modules.restrictFunctorComp (j ∣_ U) U.ι).app J.sheaf ≪≫
      (Scheme.Modules.restrictFunctor (j ∣_ U)).mapIso e ≪≫
      Scheme.Modules.restrictUnitIso (j ∣_ U)
    have e'' : J.sheaf.restrict (V.ι ≫ j) ≅ structureSheaf V.toScheme := by
      simp only [morphismRestrict_ι] at e'
      exact e'
    exact ((Scheme.Modules.restrictFunctorComp V.ι j).app J.sheaf).symm ≪≫ e''

lemma presents_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image J ι hf j U, ← Scheme.IdealSheafData.comap_comp]
  exact IdealPullback.comap_ideal I (j ≫ f) U V e

lemma invertible_restrict [IsAffine X] (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j, presents_restrict I f J ι h j⟩

end PiExponentSeshadri.InvertibleLocal

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

namespace PiExponentSeshadri.ReesGrading
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry
open SpecMaps
variable {R : Type} [CommRing R] (I : Ideal R)

lemma invertible_unique {Y : Scheme} (g h : Y ⟶ affineBlowup I)
    (f : Y ⟶ Spec (CommRingCat.of R))
    (hg : g ≫ projection I = f) (hh : h ≫ projection I = f)
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) : g = h := by
  apply Scheme.hom_ext_of_forall g h
  intro y
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  refine ⟨U.1, hyU, ?_⟩
  apply principal_unique I (U.1.ι ≫ g) (U.1.ι ≫ h) (U.1.ι ≫ f)
    (by rw [Category.assoc, hg]) (by rw [Category.assoc, hh]) r _ hr
  rwa [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr

lemma local_lift {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) (y : Y) :
    ∃ U : Y.Opens, y ∈ U ∧ ∃ h : U.toScheme ⟶ affineBlowup I,
      h ≫ projection I = U.ι ≫ f := by
  obtain ⟨U, hyU, r, hr, hIr⟩ :=
    InvertibleLocal.affine_local_equation (IdealPullback.specIdeal I) f hf y
  rw [← Scheme.IdealSheafData.comap_comp, IdealPullback.specIdeal_coordinate] at hIr
  refine ⟨U.1, hyU, principalScheme I U.1.toScheme (coordinate (U.1.ι ≫ f)).hom r hIr hr, ?_⟩
  rw [principalScheme_projection]
  exact factor (U.1.ι ≫ f)


theorem affineBlowup_universal {Y : Scheme} (f : Y ⟶ Spec (CommRingCat.of R))
    (hf : InvertiblePullbackIdeal (IdealPullback.specIdeal I) f) :
    ∃! h : Y ⟶ affineBlowup I, h ≫ projection I = f := by
  classical
  choose U hyU g hg using local_lift I f hf
  let C : Y.OpenCover := {
    I₀ := Y
    X y := (U y).toScheme
    f y := (U y).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun y => ⟨y, ?_⟩, inferInstance⟩
      simpa using hyU y }
  have hcompat (x y : C.I₀) : pullback.fst (C.f x) (C.f y) ≫ g x =
      pullback.snd (C.f x) (C.f y) ≫ g y := by
    let j := pullback.fst (C.f x) (C.f y) ≫ C.f x
    apply invertible_unique I _ _ (j ≫ f)
    · rw [Category.assoc, hg x]
      rfl
    · rw [Category.assoc, hg y]
      exact (pullback.condition_assoc f).symm
    · exact InvertibleLocal.invertible_restrict (IdealPullback.specIdeal I) f hf j
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro y
    rw [← Category.assoc, C.ι_glueMorphisms]
    exact hg y
  · intro h hh
    exact invertible_unique I h _ f hh (by
      apply C.hom_ext
      intro y
      rw [← Category.assoc, C.ι_glueMorphisms]
      exact hg y) hf

end
end PiExponentSeshadri.ReesGrading

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_GlobalInvertibleIdeal
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.InvertibleLocal
noncomputable section

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}

lemma restricted_image_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (j : Z ⟶ Y) [IsOpenImmersion j] (U : Z.affineOpens) (V : X.affineOpens)
    (hUV : j ''ᵁ U.1 ≤ f ⁻¹ᵁ V.1) :
    ((restrictedInclusion J ι j).val.app (op U.1)).hom.range =
      ((I.comap f).comap j).ideal U := by
  rw [(I.comap f).ideal_comap_of_isOpenImmersion j U]
  have he := (h.2 ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ V hUV).trans
    (IdealPullback.comap_ideal I f _ V hUV).symm
  ext r
  change (∃ s, (restrictedInclusion J ι j).val.app (op U.1) s = r) ↔ _
  erw [Ideal.mem_comap, ← he]
  change (∃ s, _) ↔ ∃ s, ι.val.app (op (j ''ᵁ U.1)) s = (j.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r at hs
    rw [← hs]
    exact (congrArg (fun k : Γ(Y, j ''ᵁ U.1) ⟶ Γ(Y, j ''ᵁ U.1) =>
      k (ι.val.app (op (j ''ᵁ U.1)) s)) (j.appIso U.1).hom_inv_id).symm
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change (j.appIso U.1).hom (ι.val.app (op (j ''ᵁ U.1)) s) = r
    rw [hs]
    exact congrArg (fun k : Γ(Z, U.1) ⟶ Γ(Z, U.1) => k r) (j.appIso U.1).inv_hom_id

lemma local_equation_on_chart (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (h : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  let : Mono ι := h.1
  let g : UnitEndomorphism.unit U.1.toScheme ⟶ UnitEndomorphism.unit U.1.toScheme :=
    e.inv ≫ restrictedInclusion J ι U.1.ι
  let : Mono (restrictedInclusion J ι U.1.ι) := restrictedInclusion_mono J ι U.1.ι
  have : Mono g := mono_iso_inv_comp_p0 e (restrictedInclusion J ι U.1.ι)
  refine ⟨UnitEndomorphism.equation g ⊤, UnitEndomorphism.equation_regular g ⊤, ?_⟩
  rw [← UnitEndomorphism.image_principal g ⊤,
    ← restricted_image_on_chart J ι h U.1.ι ⟨⊤, isAffineOpen_top _⟩ V
      (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
  ext r
  change (∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) s = r) ↔
    ∃ s, (restrictedInclusion J ι U.1.ι).val.app (op ⊤) (e.inv.val.app (op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (op ⊤) s, ?_⟩
    have ht : e.inv.val.app (op ⊤) (e.hom.val.app (op ⊤) s) = s := by
      exact congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
        k.val.app (op ⊤) s) e.hom_inv_id
    rw [ht]; exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (op ⊤) s, hs⟩

lemma local_equations (hf : InvertiblePullbackIdeal I f) (y : Y) :
    ∃ U : Y.affineOpens, y ∈ U.1 ∧ ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} := by
  obtain ⟨J, ι, h⟩ := hf
  obtain ⟨W, hyW, ⟨e⟩⟩ := J.locallyRankOne y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show y ∈ W ⊓ f ⁻¹ᵁ V from ⟨hyW, hyV⟩)
  refine ⟨⟨U, hU⟩, hyU, ?_⟩
  exact local_equation_on_chart J ι h ⟨U, hU⟩ ⟨V, hV⟩
    (hUV.trans inf_le_right) (frameOfLE J.sheaf (hUV.trans inf_le_left) e)

lemma invertible_iff_local_equations :
    InvertiblePullbackIdeal I f ↔
    ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r} :=
  ⟨local_equations, invertible_of_local_equations⟩

lemma invertible_congr {X' : Scheme} {I' : X'.IdealSheafData} {f' : Y ⟶ X'}
    (he : I.comap f = I'.comap f') :
    InvertiblePullbackIdeal I f ↔ InvertiblePullbackIdeal I' f' := by
  rw [invertible_iff_local_equations, invertible_iff_local_equations, he]

end

open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X Y Z : Scheme}

lemma presents_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hf : PresentsPullbackIdeal I f J ι) (j : Z ⟶ Y) [IsOpenImmersion j] :
    PresentsPullbackIdeal I (j ≫ f) (restrictLineBundle J j) (restrictedInclusion J ι j) := by
  let : Mono ι := hf.1
  refine ⟨restrictedInclusion_mono J ι j, ?_⟩
  intro U V e
  change ((restrictedInclusion J ι j).val.app (Opposite.op U.1)).hom.range = _
  rw [restricted_image_on_chart J ι hf j U V ?_, ← Scheme.IdealSheafData.comap_comp]
  · exact IdealPullback.comap_ideal I (j ≫ f) U V e
  · rintro _ ⟨z, hz, rfl⟩
    exact e hz

lemma invertible_restrict_general (I : X.IdealSheafData) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (j : Z ⟶ Y) [IsOpenImmersion j] :
    InvertiblePullbackIdeal I (j ≫ f) := by
  obtain ⟨J, ι, h⟩ := hf
  exact ⟨restrictLineBundle J j, restrictedInclusion J ι j,
    presents_restrict_general I f J ι h j⟩

lemma invertible_of_cover (I : X.IdealSheafData) (f : Y ⟶ X) (C : Y.OpenCover)
    (hf : ∀ i, InvertiblePullbackIdeal I (C.f i ≫ f)) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      let i := C.idx y
      obtain ⟨z, hz⟩ := C.covers y
      obtain ⟨U, hzU, r, hr, hIr⟩ := local_equations (hf i) z
      let j := U.1.ι ≫ C.f i
      have he : ((I.comap f).comap j).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
          Ideal.span {r} := by
        simpa only [j, Scheme.IdealSheafData.comap_comp] using hIr
      obtain ⟨e⟩ := IdealModule.frame_restriction (I.comap f) j r he hr.1
      refine ⟨j.opensRange, ?_, ⟨IdealModule.frameOnRange _ j e⟩⟩
      exact ⟨⟨z, hzU⟩, hz⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
end PiExponentSeshadri.InvertibleLocal

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_BlowupUniversalBaseChange
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

section
variable {X B Y Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.hom_ext (hπ : IsBlowup I π) (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) {g h : Y ⟶ B}
    (hg : g ≫ π = f) (hh : h ≫ π = f) : g = h := by
  obtain ⟨l, _, hl⟩ := hπ.2 Y f hf
  exact (hl g hg).trans (hl h hh).symm

lemma IsBlowup.postIso (hπ : IsBlowup I π) (e : X ≅ Z)
    (J : Z.IdealSheafData) (he : J.comap e.hom = I) :
    IsBlowup J (π ≫ e.hom) := by
  have hcongr (W : Scheme) (f : W ⟶ X) :
      InvertiblePullbackIdeal J (f ≫ e.hom) ↔ InvertiblePullbackIdeal I f :=
    InvertibleLocal.invertible_congr (by rw [Scheme.IdealSheafData.comap_comp, he])
  refine ⟨(hcongr B π).mpr hπ.1, ?_⟩
  intro W f hf
  have hf' : InvertiblePullbackIdeal I (f ≫ e.inv) := by
    apply (hcongr W (f ≫ e.inv)).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ e.inv) hf'
  refine ⟨l, ?_, ?_⟩
  · change l ≫ π ≫ e.hom = f
    rw [← Category.assoc, hl, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · intro m hm
    apply huniq m
    rw [← cancel_mono e.hom, Category.assoc, hm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]

lemma IsBlowup.open_baseChange (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] :
    IsBlowup (I.comap j) (pullback.fst j π) := by
  have hcongr {W : Scheme} (g : W ⟶ Z) :
      InvertiblePullbackIdeal (I.comap j) g ↔ InvertiblePullbackIdeal I (g ≫ j) :=
    InvertibleLocal.invertible_congr (Scheme.IdealSheafData.comap_comp I g j).symm
  have hpic : InvertiblePullbackIdeal (I.comap j) (pullback.fst j π) := by
    apply (hcongr _).mpr
    rw [pullback.condition]
    exact InvertibleLocal.invertible_restrict_general I π hπ.1 (pullback.snd j π)
  refine ⟨hpic, ?_⟩
  intro W f hf
  obtain ⟨l, hl, huniq⟩ := hπ.2 W (f ≫ j) ((hcongr f).mp hf)
  refine ⟨pullback.lift f l hl.symm, pullback.lift_fst _ _ _, ?_⟩
  intro m hm
  apply pullback.hom_ext
  · simpa only [pullback.lift_fst] using hm
  · rw [pullback.lift_snd]
    apply huniq
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]

def IsBlowup.iso {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : B ≅ B' where
  hom := (hπ'.2 B π hπ.1).choose
  inv := (hπ.2 B' π' hπ'.1).choose
  hom_inv_id := by
    apply hπ.hom_ext π hπ.1
    · rw [Category.assoc, (hπ.2 B' π' hπ'.1).choose_spec.1]
      exact (hπ'.2 B π hπ.1).choose_spec.1
    · simp
  inv_hom_id := by
    apply hπ'.hom_ext π' hπ'.1
    · rw [Category.assoc, (hπ'.2 B π hπ.1).choose_spec.1]
      exact (hπ.2 B' π' hπ'.1).choose_spec.1
    · simp

@[reassoc (attr := simp)]
lemma IsBlowup.iso_hom_comp {B' : Scheme} {π' : B' ⟶ X} (hπ : IsBlowup I π)
    (hπ' : IsBlowup I π') : (hπ.iso hπ').hom ≫ π' = π :=
  (hπ'.2 B π hπ.1).choose_spec.1

end

section
variable {X B B' Z : Scheme} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.baseChangeSquare (hπ : IsBlowup I π) (j : Z ⟶ X)
    [IsOpenImmersion j] (ρ : B' ⟶ Z) (hρ : IsBlowup (I.comap j) ρ)
    (β : B' ⟶ B) (hβ : β ≫ π = ρ ≫ j) : IsPullback ρ β j π := by
  let e := hρ.iso (hπ.open_baseChange j)
  refine IsPullback.of_iso_pullback ⟨hβ.symm⟩ e
    (hρ.iso_hom_comp (hπ.open_baseChange j)) ?_
  apply hπ.hom_ext (ρ ≫ j)
  · exact (InvertibleLocal.invertible_congr
      (Scheme.IdealSheafData.comap_comp I ρ j)).mpr hρ.1
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      hρ.iso_hom_comp (hπ.open_baseChange j)]
  · exact hβ

end

open TopologicalSpace
open PiExponentSeshadri.Frames
variable {X B B' : Scheme.{0}} {I : X.IdealSheafData} {π : B ⟶ X}

lemma IsBlowup.preIso (hπ : IsBlowup I π) (e : B' ≅ B) :
    IsBlowup I (e.hom ≫ π) := by
  refine ⟨InvertibleLocal.invertible_restrict_general I π hπ.1 e.hom,?_⟩
  intro Y f hf
  obtain ⟨g,hg,huniq⟩ := hπ.2 Y f hf
  refine ⟨g ≫ e.inv,by simp only [Category.assoc,Iso.inv_hom_id_assoc,hg],?_⟩
  intro g' hg'
  rw [← cancel_mono e.hom]
  simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using huniq (g' ≫ e.hom) hg'

lemma IsBlowup.morphismRestrict (hπ : IsBlowup I π) (U : X.Opens) :
    IsBlowup (I.comap U.ι) (π ∣_ U) := by
  have H := (hπ.open_baseChange U.ι).preIso (isPullback_morphismRestrict π U).isoPullback
  rwa [(isPullback_morphismRestrict π U).isoPullback_hom_fst] at H

end
end PiExponentSeshadri.Geometry

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

namespace PiExponentSeshadri.Geometry
open CategoryTheory AlgebraicGeometry

theorem rees_isBlowup {R : Type} [CommRing R] (I : Ideal R) :
    IsBlowup (IdealPullback.specIdeal I) (ReesGrading.projection I) :=
  ⟨ReesGrading.exceptional_invertible I, fun _ f hf =>
    ReesGrading.affineBlowup_universal I f hf⟩

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.AffineBlowup
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsAffine X] (I : X.IdealSheafData)

abbrev scheme : Scheme := ReesGrading.affineBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)

def projection : scheme I ⟶ X :=
  ReesGrading.projection (I.ideal ⟨⊤, isAffineOpen_top X⟩) ≫ X.isoSpec.inv

theorem isBlowup : IsBlowup I (projection I) :=
  (rees_isBlowup (I.ideal ⟨⊤, isAffineOpen_top X⟩)).postIso X.isoSpec.symm I
    (IdealPullback.comap_isoSpec_inv I)

end PiExponentSeshadri.AffineBlowup

namespace PiExponentSeshadri.BlowupGluing

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

attribute [local instance] OAI.PiExponentSeshadri.BlowupGluing.localAffine
abbrev localScheme (U : X.AffineZariskiSite) : Scheme :=
  AffineBlowup.scheme (localCentre I U)

abbrev localProjection (U : X.AffineZariskiSite) : localScheme I U ⟶ U.toOpens.toScheme :=
  AffineBlowup.projection (localCentre I U)

lemma local_isBlowup (U : X.AffineZariskiSite) :
    IsBlowup (localCentre I U) (localProjection I U) :=
  AffineBlowup.isBlowup (localCentre I U)

lemma local_invertible {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    InvertiblePullbackIdeal (localCentre I V)
      (localProjection I U ≫ (baseCover I).trans h) := by
  apply (InvertibleLocal.invertible_congr (I' := localCentre I U)
    (f' := localProjection I U) ?_).mpr (local_isBlowup I U).1
  rw [Scheme.IdealSheafData.comap_comp, centre_transition]

def transition {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    localScheme I U ⟶ localScheme I V :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose

@[reassoc (attr := simp)]
lemma transition_projection {U V : X.AffineZariskiSite} (h : U ⟶ V) :
    transition I h ≫ localProjection I V = localProjection I U ≫ (baseCover I).trans h :=
  ((local_isBlowup I V).2 _ _ (local_invertible I h)).choose_spec.1

lemma transition_id (U : X.AffineZariskiSite) : transition I (𝟙 U) = 𝟙 (localScheme I U) := by
  apply (local_isBlowup I U).hom_ext (localProjection I U) (local_isBlowup I U).1
  · rw [transition_projection, Scheme.Cover.trans_id (baseCover I) U, Category.comp_id]
  · simp

lemma transition_comp {U V W : X.AffineZariskiSite} (h : U ⟶ V) (k : V ⟶ W) :
    transition I (h ≫ k) = transition I h ≫ transition I k := by
  apply (local_isBlowup I W).hom_ext _ (local_invertible I (h ≫ k))
  · exact transition_projection I (h ≫ k)
  · rw [Category.assoc, transition_projection, ← Category.assoc, transition_projection,
      Category.assoc, Scheme.Cover.trans_comp (baseCover I) h k]

def diagram : X.AffineZariskiSite ⥤ Scheme where
  obj := localScheme I
  map := transition I
  map_id := transition_id I
  map_comp := transition_comp I

def diagramMap : diagram I ⟶ (baseCover I).functorOfLocallyDirected where
  app := localProjection I
  naturality _ _ h := transition_projection I h

lemma diagramMap_equifibered : (diagramMap I).Equifibered := by
  intro U V h
  apply IsPullback.flip
  change IsPullback (localProjection I U) (transition I h)
    ((baseCover I).trans h) (localProjection I V)
  apply (local_isBlowup I V).baseChangeSquare ((baseCover I).trans h)
    (localProjection I U)
  · rw [centre_transition]
    exact local_isBlowup I U
  · exact transition_projection I h

def gluing : (baseCover I).RelativeGluingData where
  functor := diagram I
  natTrans := diagramMap I
  equifibered := diagramMap_equifibered I

abbrev scheme : Scheme := (gluing I).glued
abbrev projection : scheme I ⟶ X := (gluing I).toBase
abbrev cover : (scheme I).OpenCover := (gluing I).cover

@[reassoc (attr := simp)]
lemma cover_projection (U : X.AffineZariskiSite) :
    (cover I).f U ≫ projection I = localProjection I U ≫ U.toOpens.ι :=
  (gluing I).ι_toBase U

lemma local_pullback (U : X.AffineZariskiSite) :
    IsPullback (localProjection I U) ((cover I).f U) U.toOpens.ι (projection I) :=
  (gluing I).isPullback_natTrans_ι_toBase U

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

lemma projection_invertible : InvertiblePullbackIdeal I (projection I) := by
  apply InvertibleLocal.invertible_of_cover I (projection I) (cover I)
  intro U
  erw [cover_projection]
  apply (InvertibleLocal.invertible_congr
    (Scheme.IdealSheafData.comap_comp I (localProjection I U) U.toOpens.ι)).mpr
  exact (local_isBlowup I U).1

lemma test_invertible {Y : Scheme.{0}} (f : Y ⟶ X)
    (hf : InvertiblePullbackIdeal I f) (U : X.AffineZariskiSite) :
    InvertiblePullbackIdeal (localCentre I U) (pullback.snd f U.toOpens.ι) := by
  apply (InvertibleLocal.invertible_congr (I' := I)
    (f' := pullback.fst f U.toOpens.ι ≫ f) ?_).mpr
  · exact InvertibleLocal.invertible_restrict_general I f hf (pullback.fst f U.toOpens.ι)
  · change ((I.comap U.toOpens.ι).comap (pullback.snd f U.toOpens.ι)) = _
    rw [← Scheme.IdealSheafData.comap_comp, pullback.condition]

lemma hom_ext {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f)
    (g h : Y ⟶ scheme I) (hg : g ≫ projection I = f) (hh : h ≫ projection I = f) : g = h := by
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  apply C.hom_ext
  intro U
  let s := pullback.snd f U.toOpens.ι
  let t := pullback.fst f U.toOpens.ι
  have eg : s ≫ U.toOpens.ι = (t ≫ g) ≫ projection I := by
    rw [Category.assoc, hg]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  have eh : s ≫ U.toOpens.ι = (t ≫ h) ≫ projection I := by
    rw [Category.assoc, hh]
    exact (pullback.condition (f := f) (g := U.toOpens.ι)).symm
  let g' := (local_pullback I U).lift s (t ≫ g) eg
  let h' := (local_pullback I U).lift s (t ≫ h) eh
  have he : g' = h' := (local_isBlowup I U).hom_ext s (test_invertible I f hf U)
    ((local_pullback I U).lift_fst _ _ _) ((local_pullback I U).lift_fst _ _ _)
  have he' := congrArg (fun k : C.X U ⟶ localScheme I U => k ≫ (cover I).f U) he
  change t ≫ g = t ≫ h
  exact ((local_pullback I U).lift_snd s (t ≫ g) eg).symm.trans
    (he'.trans ((local_pullback I U).lift_snd s (t ≫ h) eh))

theorem universal {Y : Scheme.{0}} (f : Y ⟶ X) (hf : InvertiblePullbackIdeal I f) :
    ∃! h : Y ⟶ scheme I, h ≫ projection I = f := by
  classical
  let C : Y.OpenCover := (baseCover I).pullback₁ f
  let l (U : X.AffineZariskiSite) : C.X U ⟶ localScheme I U :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose
  have hl (U : X.AffineZariskiSite) : l U ≫ localProjection I U = pullback.snd f U.toOpens.ι :=
    ((local_isBlowup I U).2 _ _ (test_invertible I f hf U)).choose_spec.1
  let g (U : C.I₀) : C.X U ⟶ scheme I := l U ≫ (cover I).f U
  have hg (U : C.I₀) : g U ≫ projection I = C.f U ≫ f := by
    dsimp only [g]
    exact (Category.assoc (l U) ((cover I).f U) (projection I)).trans
      ((congrArg (fun q : localScheme I U ⟶ X => l U ≫ q)
        (cover_projection I U)).trans
        ((Category.assoc (l U) (localProjection I U) U.toOpens.ι).symm.trans
          ((congrArg (fun q : C.X U ⟶ U.toOpens.toScheme => q ≫ U.toOpens.ι)
            (hl U)).trans (pullback.condition (f := f) (g := U.toOpens.ι)).symm)))
  have hcompat (U V : C.I₀) : pullback.fst (C.f U) (C.f V) ≫ g U =
      pullback.snd (C.f U) (C.f V) ≫ g V := by
    let j := pullback.fst (C.f U) (C.f V) ≫ C.f U
    apply hom_ext I (j ≫ f)
    · exact InvertibleLocal.invertible_restrict_general I f hf j
    · rw [Category.assoc, hg]
      rfl
    · rw [Category.assoc, hg]
      exact (pullback.condition_assoc f).symm
  refine ⟨C.glueMorphisms g hcompat, ?_, ?_⟩
  · apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U
  · intro h hh
    apply hom_ext I f hf h _ hh
    apply C.hom_ext
    intro U
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms C]
    exact hg U

theorem isBlowup : IsBlowup I (projection I) :=
  ⟨projection_invertible I, fun _ f hf => universal I f hf⟩

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_GlobalBlowupRestriction
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData)

def exceptionalLineBundle : LineBundle (scheme I) := (projection_invertible I).choose

def affineRestrictionIso (U : X.affineOpens) :
    ((projection I) ⁻¹ᵁ U.1).toScheme ≅ AffineBlowup.scheme (I.comap U.1.ι) :=
  ((isBlowup I).morphismRestrict U.1).iso (AffineBlowup.isBlowup (I.comap U.1.ι))

@[reassoc (attr := simp)]
theorem affineRestrictionIso_hom_projection (U : X.affineOpens) :
    (affineRestrictionIso I U).hom ≫ AffineBlowup.projection (I.comap U.1.ι) =
      (projection I) ∣_ U.1 :=
  ((isBlowup I).morphismRestrict U.1).iso_hom_comp
    (AffineBlowup.isBlowup (I.comap U.1.ι))

end PiExponentSeshadri.BlowupGluing

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_LinePowerLaws
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v

namespace PiExponentSeshadri.Geometry

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory BraidedCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma sheafification_tensor_left_isIso
    {P Q : PresheafOfModules X.ringCatSheaf.obj} (f : P ⟶ Q) (L : LineBundle X)
    [IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)] :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) (𝟙 L.sheaf.val) f)) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  have : IsIso (F.map (f ⊗ₘ 𝟙 L.sheaf.val)) := sheafification_tensor_right_isIso f L
  let : IsIso (F.map (β_ L.sheaf.val P).hom) :=
    (F.mapIso (β_ L.sheaf.val P)).isIso_hom
  have h : IsIso (F.map ((𝟙 L.sheaf.val ⊗ₘ f) ≫ (β_ L.sheaf.val Q).hom)) := by
    rw [braiding_naturality, F.map_comp]
    exact (inferInstance : IsIso (C := X.Modules)
      (F.map (β_ L.sheaf.val P).hom ≫ F.map (f ⊗ₘ 𝟙 L.sheaf.val)))
  rw [F.map_comp] at h
  exact (isIso_comp_right_iff _ _).mp h

def sheafificationTensorLeft (P : PresheafOfModules X.ringCatSheaf.obj)
    (L : LineBundle X) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) L.sheaf.val P) ≅
    moduleTensor X L.sheaf
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P) := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : IsIso (F.map η) :=
    isIso_of_comp_hom_eq_id _
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).left_triangle_components P)
  let ht : IsIso (F.map (PresheafOfModules.Monoidal.tensorHom
      (R := X.presheaf) (𝟙 L.sheaf.val) η)) := sheafification_tensor_left_isIso η L
  exact @asIso _ _ _ _ (F.map (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
    (𝟙 L.sheaf.val) η)) ht

def lineTensorAssoc (L M N : LineBundle X) :
    moduleTensor X (moduleTensor X L.sheaf M.sheaf) N.sheaf ≅
      moduleTensor X L.sheaf (moduleTensor X M.sheaf N.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory (R := X.presheaf)
  exact (sheafificationTensorRight (L.sheaf.val ⊗ M.sheaf.val) N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (α_ L.sheaf.val M.sheaf.val N.sheaf.val) ≪≫
    sheafificationTensorLeft (M.sheaf.val ⊗ N.sheaf.val) L

end PiExponentSeshadri.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_WeightedCompactificationImmersion
attribute [-instance] _root_.OAI.PiExponent.WeightedCompactification.affineChartMap_isOpenImmersion _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
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

instance projectiveMonomialMap_isClosedImmersion (a : σ → ι →₀ ℕ) :
    IsClosedImmersion (projectiveMonomialMap (R := R) a) := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun s : σ => Proj.basicOpen (homogeneousSubmodule σ R) (X s)) (standardChart_cover)
  intro s
  rw [projectiveMonomialMap_restrict]
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Away.map (gradedImageMap (R := R) a) (X s)))) :=
    IsClosedImmersion.spec_of_surjective _
      (homogeneousAway_map_surjective (gradedImageMap a) (gradedImageMap_surjective a)
        (isHomogeneous_X R s))
  let eB := Proj.basicOpenIsoSpec (imageGrade (R := R) a) ((gradedImageMap a) (X s))
    ((gradedImageMap a).map_mem (isHomogeneous_X R s)) (by decide)
  let eA := Proj.basicOpenIsoSpec (homogeneousSubmodule σ R) (X s)
    (isHomogeneous_X R s) (by decide)
  change IsClosedImmersion (eB.hom ≫ _ ≫ eA.inv)
  have : IsClosedImmersion eB.hom := inferInstance
  have : IsClosedImmersion eA.inv := inferInstance
  exact IsClosedImmersion.comp _ _

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


theorem affineChartMap_comp_projectiveMonomialMap
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := R) a z hz coordinate hcoordinate ≫ projectiveMonomialMap a =
      fromUnitCoordinate (affineMonomialMap (R := R) a) (by decide) (poly_X_mem z)
        (by simp [affineMonomialMap, hz]) := by
  have hchart : affineChartMap (R := R) a z hz coordinate hcoordinate =
      Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
        Proj.awayι (imageGrade (R := R) a) (imageCoordinate (R := R) a z) (imageCoordinate_mem a z) (by decide) := by
    rfl
  rw [hchart, Category.assoc]
  have hmap := Proj.awayι_comp_map (gradedImageMap (R := R) a)
    (gradedMap_irrelevant_le_map _ (gradedImageMap_surjective a))
    (by decide : 0 < (1 : ℕ)) (X z) (poly_X_mem z)
  change Spec.map (CommRingCat.ofHom (chartEvaluation (R := R) a z hz)) ≫
    (Proj.awayι (imageGrade (R := R) a) ((gradedImageMap (R := R) a) (X z))
      ((gradedImageMap (R := R) a).map_mem (poly_X_mem z)) (by decide) ≫
        Proj.map (gradedImageMap (R := R) a) _) = _
  erw [hmap]
  erw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    chartEvaluation_comp_awayMap]
  rfl

end PiExponent.WeightedCompactification

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_CurveMonomialMap
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveMonomialMap
open AlgebraicGeometry CategoryTheory MvPolynomial
open PiExponentSeshadri.Projective
open WeightedCompactification
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fromUnitCoordinate_projection
    {F E σ : Type u} [CommRing F] [CommRing E]
    (k : F →+* E) (y : σ → E) (z : σ) (hz : y z = 1) :
    fromUnitCoordinate (eval₂Hom k y) (by decide) (poly_X_mem z)
      (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E))) ≫
      polynomialProjectiveProjection F σ = Spec.map (CommRingCat.ofHom k) := by
  simp only [fromUnitCoordinate, polynomialProjectiveProjection, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change IsLocalization.Away.lift (X z)
    (by simpa only [eval₂Hom_X', hz] using (isUnit_one : IsUnit (1 : E)))
    (algebraMap (MvPolynomial σ F) (Localization.Away (X z)) (C c)) = k c
  rw [IsLocalization.Away.lift_eq, eval₂Hom_C]

theorem affineChartMap_projection
    {F ι σ : Type u} [CommRing F]
    (a : σ → ι →₀ ℕ) (z : σ) (hz : a z = 0)
    (coordinate : ι → σ) (hcoordinate : ∀ i, a (coordinate i) = Finsupp.single i 1) :
    affineChartMap (R := F) a z hz coordinate hcoordinate ≫ projection a =
      Spec.map (CommRingCat.ofHom (C : F →+* MvPolynomial ι F)) := by
  rw [projection, ← Category.assoc, affineChartMap_comp_projectiveMonomialMap]
  exact fromUnitCoordinate_projection C (fun s => monomial (a s) 1) z (by rw [hz]; exact MvPolynomial.C_1)

end PiExponent.CurveMonomialMap

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Approximation_TwistSections
attribute [-instance] _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {X : Scheme}

def moduleSectionMultiplyRight (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) : M ⟶ moduleTensor X M L :=
  (moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s

@[reassoc] theorem moduleSectionMultiplyRight_natural {M N L : X.Modules}
    (f : M ⟶ N) (s : structureSheaf X ⟶ L) :
    f ≫ moduleSectionMultiplyRight N s =
      moduleSectionMultiplyRight M s ≫ moduleTensorMap f (𝟙 L) := by
  have h : f ≫ (moduleTensorRightUnit N).inv =
      (moduleTensorRightUnit M).inv ≫ moduleTensorMap f (𝟙 (structureSheaf X)) := by
    apply (cancel_mono (moduleTensorRightUnit N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [moduleTensorRightUnit_natural]
    simp
  unfold moduleSectionMultiplyRight
  rw [← Category.assoc, h, Category.assoc, ← moduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← moduleTensorMap_comp]
  simp

def moduleTwistStep (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+1) where
  app M := moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s
  naturality _ _ f := moduleSectionMultiplyRight_natural ((moduleTwistFunctor L n).map f) s

def moduleTwistSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    ∀ n : ℕ, 𝟭 X.Modules ⟶ moduleTwistFunctor L n
  | 0 => 𝟙 _
  | n+1 => moduleTwistSection L s n ≫ moduleTwistStep L s n

def moduleTwistForward (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    ∀ k : ℕ, moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+k)
  | 0 => 𝟙 _
  | k+1 => moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k)

@[simp] theorem moduleTwistSection_add (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n k : ℕ) :
    moduleTwistSection L s (n+k) = moduleTwistSection L s n ≫ moduleTwistForward L s n k := by
  induction k with
  | zero => exact (Category.comp_id _).symm
  | succ k ih =>
    change moduleTwistSection L s (n+k) ≫ moduleTwistStep L s (n+k) =
      moduleTwistSection L s n ≫
        (moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k))
    rw [ih, Category.assoc]

def moduleTwistRestrictFrame (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n : ℕ, moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι
  | 0 => Iso.refl _
  | n+1 => Functor.isoWhiskerLeft (moduleTwistFunctor L n)
      (moduleTensorRestrictFrame U L.sheaf e) ≪≫ moduleTwistRestrictFrame L U e n

@[simp] theorem moduleTwistRestrictFrame_zero (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) :
    ((moduleTwistRestrictFrame L U e 0).app M).hom = 𝟙 (M.restrict U.ι) := rfl

@[simp] theorem moduleTwistRestrictFrame_succ (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) (n : ℕ) :
    ((moduleTwistRestrictFrame L U e (n+1)).app M).hom =
      ((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom ≫
        ((moduleTwistRestrictFrame L U e n).app M).hom := rfl

end
end PiExponentSeshadri.Geometry

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AdmissibleBlowupGeometry
attribute [-instance] _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.AdmissibleBlowupGeometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open WeightedGeometryScale
variable {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)

def compactificationStructureMap : compactification d ⟶ Spec (.of ℂ) :=
  WeightedCompactification.projection (exponents d)

instance affineChart_isOpenImmersion : IsOpenImmersion (affineChart d) := by
  dsimp [affineChart]
  infer_instance

def origin : CompactLogJetIdeal.affineSpace d.m :=
  ⟨WeightedBezout.pointIdeal (0 : Fin (d.m+1) → ℂ),inferInstance⟩

instance compactification_nonempty : Nonempty (compactification d) := ⟨affineChart d (origin d)⟩
instance compactification_isIntegral : IsIntegral (compactification d) := by infer_instance
instance affineChart_quasiCompact : QuasiCompact (affineChart d) := by infer_instance

theorem affineChart_over : affineChart d ≫ compactificationStructureMap d =
    CompactLogJetIdeal.structureMap d.m :=
  CurveMonomialMap.affineChartMap_projection (exponents d) (constantIndex d)
    ((scale d).exponents_constant d.curveDegreeWeights_pos)
    (coordinateIndex d) ((scale d).exponents_coordinate d.curveDegreeWeights_pos)

def hyperplane : LineBundle (compactification d) := WeightedCompactification.lineBundle (exponents d)

def logCutoff : Fin d.m → ℕ :=
  (exists_log_cutoff d.curveJetWeights (d.curveJetWeights_pos 0)).choose

def centerIdeal : (compactification d).IdealSheafData :=
  CompactLogJetIdeal.compactIdeal d.curveCenters (logCutoff d) (scale d).jetPowers (affineChart d)

abbrev blowup : Scheme := PiExponentSeshadri.BlowupGluing.scheme (centerIdeal d)
abbrev projection : blowup d ⟶ compactification d :=
  PiExponentSeshadri.BlowupGluing.projection (centerIdeal d)

def A : LineBundle (blowup d) := (hyperplane d).pullback (projection d)
abbrev J : LineBundle (blowup d) :=
  PiExponentSeshadri.BlowupGluing.exceptionalLineBundle (centerIdeal d)

end PiExponent.AdmissibleBlowupGeometry

end

end OAI
end


