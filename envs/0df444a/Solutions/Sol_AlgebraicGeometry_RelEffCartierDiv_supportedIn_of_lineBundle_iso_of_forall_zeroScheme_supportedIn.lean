-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4f01021a-6339-5845-9fef-e7e8e12380fc

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesIhomSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ofUnitSection_sectionDual_app
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensor_pullback_iso_of_trivial_on_open
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe v u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn.AlgebraicGeometry TensorProduct"

noncomputable section

namespace HavoidMC

p2m_open "CategoryTheory.MonoidalClosed"

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

def toBidual (M : C) : M ⟶ (ihom ((ihom M).obj (𝟙_ C))).obj (𝟙_ C) :=
  MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))

omit [BraidedCategory C] in
theorem unitIsoSelf_inv (X : C) :
    (MonoidalClosed.unitIsoSelf X).inv = MonoidalClosed.curry (λ_ X).hom := by
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  dsimp at h
  erw [Category.id_comp] at h
  change (conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom).app X = _
  rw [h, MonoidalClosed.curry_eq]
  try rfl

theorem toBidual_comp_pre_app_comp_unitIsoSelf_hom {M : C} (ι : M ⟶ 𝟙_ C) :
    toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ C)).hom = ι := by
  have hk : MonoidalClosed.uncurry
      (toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C)) = (λ_ M).hom ≫ ι := by
    rw [MonoidalClosed.uncurry_pre_app, toBidual, MonoidalClosed.uncurry_curry,
      BraidedCategory.braiding_naturality_left_assoc, MonoidalClosed.whiskerLeft_curry'_ihom_ev_app,
      ← Category.assoc, braiding_rightUnitor]
  have h2 : toBidual M ≫ (MonoidalClosed.pre (MonoidalClosed.curry' ι)).app (𝟙_ C) =
      ι ≫ (MonoidalClosed.unitIsoSelf (𝟙_ C)).inv := by
    rw [unitIsoSelf_inv, ← MonoidalClosed.curry_natural_left, leftUnitor_naturality, ← hk,
      MonoidalClosed.curry_uncurry]
  rw [← Category.assoc, h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end HavoidMC

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso IsOpenImmersion.lift Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.IdealSheafData.comap_mono Scheme.Modules.presheaf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.Hom IsFinite isAffine_of_isAffineHom IsAffine Spec Spec.map Scheme Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.finite_appTop IsClosedImmersion Scheme.Modules.pullbackCongr isAffineOpen_top IsClosedImmersion.isIso_of_injective_of_isAffine Scheme.fromSpecResidueField_apply IsFinite.SpecMap_iff Scheme.IdealSheafData.inclusion_subschemeι Scheme.isoSpec_inv_naturality Scheme.Modules Scheme.IdealSheafData.inclusion Scheme.Opens IsOpenImmersion.lift_fac Scheme.IdealSheafData.le_def IsClosedImmersion.isAffine_surjective_of_isAffine Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso RelEffCartierDiv mapOnProdOver mapOnProdOver_snd RelEffCartierDiv.supportedIn_pullbackAlong_iff RelEffCartierDiv.supportedIn_iff_supportedInLocus_eq_top Scheme.Modules.ofUnitSection Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.coeffIdeal Scheme.Modules.zeroSchemeIdeal Scheme.Modules.zeroSchemeIdeal_le Scheme.Modules.pullbackSection Scheme.Modules.IsInvertible Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Hom.ker_comp_of_isIso fromSpecResidueField Hom.finrank_comp_left_of_isIso Modules.Hom.zero_app Modules.pullback Opens.range_ι Hom IdealSheafData.comap_mono Modules.presheaf Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.app Hom.finrank_SpecMap_eq_finrank isoSpec_Spec_inv Hom.comp_appTop isoSpec Hom.finite_appTop residueField Hom.comp_app Modules.pullbackCongr fromSpecResidueField_apply IdealSheafData.inclusion_subschemeι isoSpec_inv_naturality Modules IdealSheafData.inclusion Opens residue IdealSheafData.le_def IdealSheafData Modules.pullbackComp ΓSpecIso Modules.ofUnitSection Modules.restrictSection Modules.coeff Modules.coeffIdeal Modules.zeroSchemeIdeal Modules.zeroSchemeIdeal_le Modules.pullbackSection Modules.IsInvertible Modules.zeroSchemeIdeal_comp_eq_of_isIso Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.zero_app pullback presheaf Hom.comp_app Hom Hom.app pullbackCongr pullbackComp tensor ofUnitSection restrictSection coeff coeffIdeal coeff_mem_coeffIdeal zeroSchemeIdeal zeroSchemeIdeal_le pullbackSection sectionDual IsInvertible ofUnitSection_sectionDual_app zeroSchemeIdeal_comp_eq_of_isIso nonempty_pullback_tensor_pullback_iso_of_trivial_on_open finrank_baseChange_sections_eq_one_of_locallyTrivial"
namespace Havoid
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

theorem le_zeroSchemeIdeal_invModuleSection {I : X.IdealSheafData}
    (hM : Scheme.Modules.IsInvertible I.invModule) :
    I ≤ zeroSchemeIdeal I.invModuleSection := by
  have hcomp : HavoidMC.toBidual I.module ≫ sectionDual I.invModuleSection = I.moduleι :=
    HavoidMC.toBidual_comp_pre_app_comp_unitIsoSelf_hom I.moduleι
  rw [Scheme.IdealSheafData.le_def]
  intro U x hx
  have hx' : x ∈ Set.range (I.moduleι.app U) := by
    rw [(I.range_moduleIota_app_and_injective U).1]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  have hy : (sectionDual I.invModuleSection).app U.1
      ((HavoidMC.toBidual I.module).app U.1 y) = I.moduleι.app U.1 y := by
    change ((HavoidMC.toBidual I.module).app U.1 ≫
      (sectionDual I.invModuleSection).app U.1) y = _
    rw [← Scheme.Modules.Hom.comp_app, hcomp]
  change ofUnitSection U.1 (I.moduleι.app U.1 y) ∈ (zeroSchemeIdeal I.invModuleSection).ideal U
  rw [← hy, ofUnitSection_sectionDual_app]
  exact (hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq _).1 U (coeff_mem_coeffIdeal _ U.1 _)

end AlgebraicGeometry.Scheme.Modules.Havoid

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom.ker_comp_of_isIso IsOpenImmersion.lift Surjective Scheme.Hom.finrank_comp_left_of_isIso Scheme.Modules.Hom.zero_app Scheme.Modules.pullback Scheme.Opens.range_ι Scheme.Hom Scheme.IdealSheafData.comap_mono Scheme.Modules.presheaf Scheme.Modules.Hom.comp_app Flat.SpecMap_iff Scheme.Modules.Hom IsFinite isAffine_of_isAffineHom IsAffine Spec Spec.map Scheme Scheme.Modules.Hom.app Scheme.Hom.finrank_SpecMap_eq_finrank Scheme.isoSpec_Spec_inv IsOpenImmersion Scheme.Hom.comp_appTop Flat Scheme.Hom.finite_appTop IsClosedImmersion Scheme.Modules.pullbackCongr isAffineOpen_top IsClosedImmersion.isIso_of_injective_of_isAffine Scheme.fromSpecResidueField_apply IsFinite.SpecMap_iff Scheme.IdealSheafData.inclusion_subschemeι Scheme.isoSpec_inv_naturality Scheme.Modules Scheme.IdealSheafData.inclusion Scheme.Opens IsOpenImmersion.lift_fac Scheme.IdealSheafData.le_def IsClosedImmersion.isAffine_surjective_of_isAffine Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.ΓSpecIso RelEffCartierDiv mapOnProdOver mapOnProdOver_snd RelEffCartierDiv.supportedIn_pullbackAlong_iff RelEffCartierDiv.supportedIn_iff_supportedInLocus_eq_top Scheme.Modules.ofUnitSection Scheme.Modules.restrictSection Scheme.Modules.coeff Scheme.Modules.coeffIdeal Scheme.Modules.zeroSchemeIdeal Scheme.Modules.zeroSchemeIdeal_le Scheme.Modules.pullbackSection Scheme.Modules.IsInvertible Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial"
namespace Havoid
p2m_open "AlgebraicGeometry"

theorem injective_of_surjective_of_finrank_eq {K A B : Type*} [Field K] [CommRing A] [CommRing B]
    (φA : K →+* A) (φB : K →+* B) (g : A →+* B) (hg : g.comp φA = φB)
    (hsurj : Function.Surjective g) (hA : φA.Finite) (hB : φB.Finite)
    (x : PrimeSpectrum K) (hrk : φA.finrank x = φB.finrank x) : Function.Injective g := by
  algebraize [φA, φB]
  have hA' : Module.finrank K A = φA.finrank x := by
    rw [← RingHom.algebraMap_toAlgebra φA, RingHom.finrank_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]
  have hB' : Module.finrank K B = φB.finrank x := by
    rw [← RingHom.algebraMap_toAlgebra φB, RingHom.finrank_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Nat.cast_id]
  let gl : A →ₗ[K] B :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun r a => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.id_apply]
        congr 1
        exact DFunLike.congr_fun hg r }
  have hfr : Module.finrank K A = Module.finrank K B := by rw [hA', hB', hrk]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr (f := gl)).mpr hsurj

theorem finrank_eq_finrank_appTop {Z : Scheme.{u}} {R : CommRingCat.{u}} (p : Z ⟶ Spec R)
    [IsAffine Z] [IsFinite p] [Flat p] :
    p.finrank = ((Scheme.ΓSpecIso R).inv ≫ p.appTop).hom.finrank := by
  have e : Z.isoSpec.inv ≫ p = Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have h1 : IsFinite (Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop)) := by
    rw [← e]; infer_instance
  have h2 : Flat (Spec.map ((Scheme.ΓSpecIso R).inv ≫ p.appTop)) := by
    rw [← e]; infer_instance
  rw [IsFinite.SpecMap_iff] at h1
  rw [Flat.SpecMap_iff] at h2
  rw [← Scheme.Hom.finrank_comp_left_of_isIso Z.isoSpec.inv p, e,
    Scheme.Hom.finrank_SpecMap_eq_finrank h1 h2]

theorem IdealSheafData_eq_of_le_of_finrank_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (q : X ⟶ Spec (CommRingCat.of k)) {I J : X.IdealSheafData} (h : I ≤ J)
    [IsFinite (I.subschemeι ≫ q)] [Flat (I.subschemeι ≫ q)]
    [IsFinite (J.subschemeι ≫ q)] [Flat (J.subschemeι ≫ q)]
    (hrk : ∃ t, (I.subschemeι ≫ q).finrank t = (J.subschemeι ≫ q).finrank t) : I = J := by
  obtain ⟨t, ht⟩ := hrk
  have hi : Scheme.IdealSheafData.inclusion h ≫ I.subschemeι = J.subschemeι :=
    Scheme.IdealSheafData.inclusion_subschemeι h
  haveI : IsAffine I.subscheme := isAffine_of_isAffineHom (I.subschemeι ≫ q)
  haveI : IsAffine J.subscheme := isAffine_of_isAffineHom (J.subschemeι ≫ q)
  suffices IsIso (Scheme.IdealSheafData.inclusion h) by
    rw [← I.ker_subschemeι, ← J.ker_subschemeι, ← hi, Scheme.Hom.ker_comp_of_isIso]
  refine IsClosedImmersion.isIso_of_injective_of_isAffine ?_
  have hij : Scheme.IdealSheafData.inclusion h ≫ I.subschemeι ≫ q = J.subschemeι ≫ q := by
    rw [← Category.assoc, hi]
  have hcomp : (Scheme.IdealSheafData.inclusion h).appTop.hom.comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (I.subschemeι ≫ q).appTop).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (J.subschemeι ≫ q).appTop).hom := by
    rw [← CommRingCat.hom_comp, Category.assoc, ← Scheme.Hom.comp_appTop, hij]
  refine injective_of_surjective_of_finrank_eq _ _ _ hcomp
    (IsClosedImmersion.isAffine_surjective_of_isAffine _).2 ?_ ?_ t ?_
  · rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp (Scheme.Hom.finite_appTop _)
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  · rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp (Scheme.Hom.finite_appTop _)
      (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  · rw [← finrank_eq_finrank_appTop, ← finrank_eq_finrank_appTop]
    exact ht

theorem RelEffCartierDiv_I_eq_of_le
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) {g : ℕ}
    (D E : RelEffCartierDiv c g x) (hle : D.I ≤ E.I) : D.I = E.I := by
  have := D.isFinite
  have := D.flat
  have := E.isFinite
  have := E.flat
  obtain ⟨t⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
  exact IdealSheafData_eq_of_le_of_finrank_eq (pullback.snd c x) hle
    ⟨t, by rw [D.finrank_eq, E.finrank_eq]⟩

def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

theorem exists_section_ne_zero_of_isAffine {X : Scheme.{u}} [IsAffine X] [Nonempty ↥X]
    {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) : ∃ σ : Γ(M, ⊤), σ ≠ 0 := by
  classical

  haveI : Nontrivial Γ(X, ⊤) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨X.isoSpec.hom.base (Classical.arbitrary _)⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(X, ⊤)
  letI := Ideal.Quotient.field m

  have h1 := Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial M hM.1 ⟨⊤, isAffineOpen_top X⟩
    (Γ(X, ⊤) ⧸ m)
  by_contra h
  push Not at h
  haveI : Subsingleton Γ(M, ⊤) := subsingleton_of_forall_eq 0 h
  haveI : Subsingleton ((Γ(X, ⊤) ⧸ m) ⊗[Γ(X, ⊤)] Γ(M, (⊤ : X.Opens))) := inferInstance
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

theorem exists_section_ne_zero_of_I_eq_bot
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) {g : ℕ}
    (D : RelEffCartierDiv c g x) (hD : D.I = ⊥) [Nonempty ↥(pullback c x)]
    {M : (pullback c x).Modules} (hM : Scheme.Modules.IsInvertible M) :
    ∃ σ : 𝟙_ (pullback c x).Modules ⟶ M, σ ≠ 0 := by

  have hfin := D.isFinite
  rw [hD] at hfin
  haveI : IsFinite (pullback.snd c x) := by
    have h : pullback.snd c x = inv (⊥ : (pullback c x).IdealSheafData).subschemeι ≫
        ((⊥ : (pullback c x).IdealSheafData).subschemeι ≫ pullback.snd c x) := by simp
    rw [h]; infer_instance
  haveI : IsAffine (pullback c x) := isAffine_of_isAffineHom (pullback.snd c x)
  obtain ⟨σ, hσ⟩ := exists_section_ne_zero_of_isAffine hM
  exact exists_hom_ne_zero M σ hσ

theorem isInvertible_of_iso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M')
    (hM : Scheme.Modules.IsInvertible M) : Scheme.Modules.IsInvertible M' := by
  refine ⟨fun z => ?_⟩
  obtain ⟨U, hzU, ⟨eU⟩⟩ := hM.exists_trivialization z
  exact ⟨U, hzU, ⟨((Scheme.Modules.pullback U.ι).mapIso e).symm ≪≫ eU⟩⟩

theorem zeroSchemeIdeal_zero {X : Scheme.{u}} {M : X.Modules} :
    Scheme.Modules.zeroSchemeIdeal (0 : 𝟙_ X.Modules ⟶ M) = ⊥ := by
  refine le_antisymm (Scheme.Modules.zeroSchemeIdeal_le fun U => ?_) bot_le
  rw [Scheme.Modules.coeffIdeal, Ideal.span_le]
  rintro _ ⟨φ, rfl⟩
  have h0 : Scheme.Modules.restrictSection (0 : 𝟙_ X.Modules ⟶ M) U.1 = 0 := rfl
  simp only [SetLike.mem_coe, Scheme.Modules.coeff, h0, map_zero]
  first
    | exact Ideal.zero_mem _
    | (rw [show Scheme.Modules.ofUnitSection ⊤ (0 : Γ(𝟙_ ((U.1 : Scheme.{u})).Modules, ⊤)) = 0 from rfl, map_zero]
       exact Ideal.zero_mem _)

theorem fibre
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {g : ℕ} (D₀ : RelEffCartierDiv c g t) (N : T.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hiso : Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N))
    (hZ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (D₀.pullbackAlong x rfl).SupportedIn U := by
  classical
  set F := mapOnProdOver c x rfl with hF
  set q := pullback.snd c t with hq

  obtain ⟨e₀⟩ := hiso
  have hP : Scheme.Modules.IsInvertible (M ⊗ (Scheme.Modules.pullback q).obj N) := hM.tensor (hN.pullback q)
  have hL : Scheme.Modules.IsInvertible D₀.lineBundle := isInvertible_of_iso e₀.symm hP
  set s : 𝟙_ (pullback c t).Modules ⟶ M ⊗ (Scheme.Modules.pullback q).obj N := D₀.I.invModuleSection ≫ e₀.hom with hs
  have hJ : D₀.I ≤ Scheme.Modules.zeroSchemeIdeal s := by
    rw [hs, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]
    exact Scheme.Modules.Havoid.le_zeroSchemeIdeal_invModuleSection hL

  set σ₀ := Scheme.Modules.pullbackSection F s with hσ₀
  have hZσ₀ : Scheme.Modules.zeroSchemeIdeal σ₀ = (Scheme.Modules.zeroSchemeIdeal s).comap F :=
    (hP.comap_zeroSchemeIdeal F s).symm

  obtain ⟨V, hyV, ⟨eV⟩⟩ := hN.exists_trivialization (x.base (IsLocalRing.closedPoint k))
  obtain ⟨eT⟩ := Scheme.Modules.nonempty_pullback_tensor_pullback_iso_of_trivial_on_open q V M N eV
  have hrange : Set.range F.base ⊆ Set.range (q ⁻¹ᵁ V).ι.base := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change q.base (F.base z) ∈ (V : Set T)
    rw [show q.base (F.base z) = (F ≫ q).base z from rfl, hF, hq, mapOnProdOver_snd]
    change x.base ((pullback.snd c (x ≫ t)).base z) ∈ (V : Set T)
    have : (pullback.snd c (x ≫ t)).base z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rw [this]
    exact hyV
  set F' := IsOpenImmersion.lift (q ⁻¹ᵁ V).ι F hrange with hF'
  have hF'F : F' ≫ (q ⁻¹ᵁ V).ι = F := IsOpenImmersion.lift_fac _ _ _
  let e : (Scheme.Modules.pullback F).obj (M ⊗ (Scheme.Modules.pullback q).obj N) ≅
      (Scheme.Modules.pullback F).obj M :=
    (Scheme.Modules.pullbackCongr hF'F.symm).app _ ≪≫ ((Scheme.Modules.pullbackComp F' (q ⁻¹ᵁ V).ι).app _).symm ≪≫
      (Scheme.Modules.pullback F').mapIso eT ≪≫ (Scheme.Modules.pullbackComp F' (q ⁻¹ᵁ V).ι).app _ ≪≫
      (Scheme.Modules.pullbackCongr hF'F).app _
  set σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback F).obj M := σ₀ ≫ e.hom with hσdef
  have hZσ : Scheme.Modules.zeroSchemeIdeal σ = Scheme.Modules.zeroSchemeIdeal σ₀ :=
    Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso σ₀ e.hom
  have hle : (D₀.pullbackAlong x rfl).I ≤ Scheme.Modules.zeroSchemeIdeal σ := by
    rw [hZσ, hZσ₀]
    exact Scheme.IdealSheafData.comap_mono F hJ

  have transfer : ∀ Dx : RelEffCartierDiv c g (x ≫ t), Dx.SupportedIn U →
      (D₀.pullbackAlong x rfl).I = Dx.I → (D₀.pullbackAlong x rfl).SupportedIn U := by
    intro Dx hDxU hI z hz
    apply hDxU
    change z ∈ (Dx.I.support : Set _)
    rw [← hI]
    exact hz
  by_cases hσ : σ = 0
  ·
    have hbot : (D₀.pullbackAlong x rfl).I = ⊥ := by
      apply le_bot_iff.mp
      rw [hσ, zeroSchemeIdeal_zero] at hle
      exact hle
    rcases isEmpty_or_nonempty ↥(pullback c (x ≫ t)) with hE | hNE
    · intro z _
      exact (IsEmpty.false z).elim
    · obtain ⟨τ, hτ⟩ := exists_section_ne_zero_of_I_eq_bot c (x ≫ t) (D₀.pullbackAlong x rfl) hbot (hM.pullback F)
      obtain ⟨Dx, hDxI, hDxU⟩ := hZ k x τ hτ
      refine transfer Dx hDxU (RelEffCartierDiv_I_eq_of_le c (x ≫ t) _ Dx ?_)
      rw [hbot]
      exact bot_le
  · obtain ⟨Dx, hDxI, hDxU⟩ := hZ k x σ hσ
    refine transfer Dx hDxU (RelEffCartierDiv_I_eq_of_le c (x ≫ t) _ Dx ?_)
    rw [hDxI]
    exact hle

theorem main
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {g : ℕ} (D₀ : RelEffCartierDiv c g t) (N : T.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hiso : Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N))
    (hZ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) :
    D₀.SupportedIn U := by
  rw [RelEffCartierDiv.supportedIn_iff_supportedInLocus_eq_top, eq_top_iff]
  rintro y -

  let K : Type u := AlgebraicClosure (T.residueField y)
  let x : Spec (CommRingCat.of K) ⟶ T :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField y) K)) ≫ T.fromSpecResidueField y
  have hx : x.base (IsLocalRing.closedPoint K) = y := by
    change (T.fromSpecResidueField y).base _ = y
    exact Scheme.fromSpecResidueField_apply y _
  have h := fibre c U t M hM D₀ N hN hiso hZ K x
  have := (RelEffCartierDiv.supportedIn_pullbackAlong_iff D₀ U x rfl).mp h
  exact this ⟨IsLocalRing.closedPoint K, hx⟩

end AlgebraicGeometry.Havoid

end

theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) (U : C.Opens)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    {g : ℕ} (D₀ : RelEffCartierDiv c g t) (N : T.Modules) (hN : Scheme.Modules.IsInvertible N)
    (hiso : Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj N))
    (hZ : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
      (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
      ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) :
    D₀.SupportedIn U :=
  AlgebraicGeometry.Havoid.main c U t M hM D₀ N hN hiso hZ

end S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_supportedIn_of_lineBundle_iso_of_forall_zeroScheme_supportedIn (solution)
