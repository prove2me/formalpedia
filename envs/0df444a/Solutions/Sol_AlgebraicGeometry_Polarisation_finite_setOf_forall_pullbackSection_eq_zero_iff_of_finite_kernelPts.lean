-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0a85e32f-b084-5be6-bf17-c7ef21138000

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Polarisation_mem_kernelPts_iff_nonempty_pullback_translate_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_preimage_support_zeroSchemeIdeal_eq_of_forall_pullbackSection_eq_zero_iff_comp
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation TopologicalSpace"

open scoped CategoryTheory.MonObj

universe u

namespace SBSol

section grp
variable {C : Type*} [Category C] [CartesianMonoidalCategory C] (G : C) [GrpObj G]

def rt (x : 𝟙_ C ⟶ G) : G ⟶ G := 𝟙 G * (CartesianMonoidalCategory.toUnit G ≫ x)

theorem rt_mul (x y : 𝟙_ C ⟶ G) : rt G (x * y) = rt G x ≫ rt G y := by
  have h1 : CartesianMonoidalCategory.toUnit G ≫ (x * y) =
      (CartesianMonoidalCategory.toUnit G ≫ x) * (CartesianMonoidalCategory.toUnit G ≫ y) :=
    MonObj.comp_mul _ _ _
  have h2 : rt G x ≫ rt G y = (rt G x ≫ 𝟙 G) * (rt G x ≫ (CartesianMonoidalCategory.toUnit G ≫ y)) :=
    MonObj.comp_mul _ _ _
  have h3 : rt G x ≫ (CartesianMonoidalCategory.toUnit G ≫ y) = CartesianMonoidalCategory.toUnit G ≫ y := by
    rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  rw [h2, h3, Category.comp_id]
  unfold rt
  rw [h1, mul_assoc]

theorem rt_one : rt G (1 : 𝟙_ C ⟶ G) = 𝟙 G := by
  unfold rt
  rw [MonObj.comp_one, mul_one]

theorem comp_rt {T : C} (z : T ⟶ G) (x : 𝟙_ C ⟶ G) :
    z ≫ rt G x = z * (CartesianMonoidalCategory.toUnit T ≫ x) := by
  unfold rt
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit]

def rtIso (x : 𝟙_ C ⟶ G) : G ≅ G where
  hom := rt G x
  inv := rt G x⁻¹
  hom_inv_id := by rw [← rt_mul, mul_inv_cancel, rt_one]
  inv_hom_id := by rw [← rt_mul, inv_mul_cancel, rt_one]

end grp

theorem finite_maximal_irreducible_subset {α : Type*} [TopologicalSpace α] [NoetherianSpace α]
    {D : Set α} (hD : IsClosed D) :
    {C : Set α | Maximal (fun C' : Set α => IsIrreducible C' ∧ C' ⊆ D) C}.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hD
  refine hSf.subset fun C hC => ?_
  lift S to Finset (Set α) using hSf
  rcases isIrreducible_iff_sUnion_isClosed.1 hC.1.1 S hSc (hSU ▸ hC.1.2) with ⟨t, htS, ht⟩
  have htD : t ⊆ D := hSU.symm ▸ Set.subset_sUnion_of_mem htS
  rwa [ht.antisymm (hC.2 ⟨hSi _ htS, htD⟩ ht)]

theorem maximal_image {α : Type*} [TopologicalSpace α] (e : α ≃ₜ α) {D : Set α}
    (hD : e ⁻¹' D = D) {C : Set α} (hC : Maximal (fun C' : Set α => IsIrreducible C' ∧ C' ⊆ D) C) :
    Maximal (fun C' : Set α => IsIrreducible C' ∧ C' ⊆ D) (e '' C) := by
  have hD' : e '' D = D := by
    calc e '' D = e '' (e ⁻¹' D) := by rw [hD]
      _ = D := Set.image_preimage_eq D e.surjective
  have hDs : e.symm '' D = D := by
    rw [e.image_symm]; exact hD
  refine ⟨⟨hC.1.1.image e e.continuous.continuousOn, (Set.image_mono hC.1.2).trans hD'.le⟩, ?_⟩
  intro C' hC' hle
  have h1 : IsIrreducible (e.symm '' C') := hC'.1.image e.symm e.symm.continuous.continuousOn
  have h2 : e.symm '' C' ⊆ D := (Set.image_mono hC'.2).trans hDs.le
  have h3 : C ⊆ e.symm '' C' := by
    intro c hc
    refine ⟨e c, hle ⟨c, hc, rfl⟩, e.symm_apply_apply c⟩
  have h4 : e.symm '' C' ⊆ C := hC.2 ⟨h1, h2⟩ h3
  intro c' hc'
  exact ⟨e.symm c', h4 ⟨c', hc', rfl⟩, e.apply_symm_apply c'⟩

section transl
variable {k : Type} [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))

theorem left_rt_mul [GrpObj (Over.mk f)] (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :
    (rt (Over.mk f) (x * y)).left = (rt (Over.mk f) x).left ≫ (rt (Over.mk f) y).left := by
  have h := congrArg (fun φ : Over.mk f ⟶ Over.mk f => φ.left) (rt_mul (Over.mk f) x y)
  exact h

theorem left_rt_one [GrpObj (Over.mk f)] :
    (rt (Over.mk f) (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f)).left = 𝟙 A := by
  have h := congrArg (fun φ : Over.mk f ⟶ Over.mk f => φ.left) (rt_one (Over.mk f))
  exact h

theorem mul_left [GrpObj (Over.mk f)] (z x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :
    (z * x).left = z.left ≫ (rt (Over.mk f) x).left := by
  have h0' : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
      𝟙 (𝟙_ (Over (Spec (CommRingCat.of k)))) :=
    CartesianMonoidalCategory.toUnit_unique _ _
  have h0 : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ x = x := by
    rw [h0']
    exact Category.id_comp x
  have h : z ≫ rt (Over.mk f) x = z * x := by
    rw [comp_rt, h0]
  have h2 := congrArg (fun φ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f => φ.left) h
  simp only [Over.comp_left] at h2
  exact h2.symm

noncomputable def TIso [GrpObj (Over.mk f)] (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) : A ≅ A :=
  (Over.forget _).mapIso (rtIso (Over.mk f) x)

theorem TIso_hom [GrpObj (Over.mk f)] (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :
    (TIso f x).hom = (rt (Over.mk f) x).left := rfl

theorem TIso_inv [GrpObj (Over.mk f)] (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :
    (TIso f x).inv = (rt (Over.mk f) x⁻¹).left := rfl

theorem left_rt_eq_translate (L : RelativeGroupLaw k f) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :
    letI : GrpObj (Over.mk f) := L.grpObjOverMk
    (rt (Over.mk f) x).left = L.translate (overHomToSchemeHomOver x) := by
  letI : GrpObj (Over.mk f) := L.grpObjOverMk
  have h := congrArg Subtype.val (L.overHomEquivSchemeHomOver_mul (Over.mk f) (𝟙 (Over.mk f))
    (CartesianMonoidalCategory.toUnit (Over.mk f) ≫ x))
  have hw : (CartesianMonoidalCategory.toUnit (Over.mk f)).left = f := by
    simpa using Over.w (CartesianMonoidalCategory.toUnit (Over.mk f))
  have hx : x.left ≫ f = 𝟙 _ := by
    simpa using Over.w x
  have e1 : overHomEquivSchemeHomOver (Over.mk f) f (𝟙 (Over.mk f)) =
      (⟨𝟙 A, by simp⟩ : SchemeHomOver f f) := Subtype.ext rfl
  have e2 : overHomEquivSchemeHomOver (Over.mk f) f (CartesianMonoidalCategory.toUnit (Over.mk f) ≫ x) =
      (⟨f ≫ x.left, by erw [Category.assoc, Over.w x]; simp⟩ : SchemeHomOver f f) := by
    apply Subtype.ext
    simp only [overHomEquivSchemeHomOver_apply_coe, Over.comp_left, hw]
    try rfl
  rw [e1, e2] at h
  exact h
end transl

end SBSol

open SBSol in
theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (hK : (kernelPts f L 𝓜).Finite)
    (θ : 𝟙_ A.Modules ⟶ 𝓜) (hθ : θ ≠ 0) :
    letI : GrpObj (Over.mk f) := L.grpObjOverMk
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f |
        ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f,
          Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0} := by
  letI inst : GrpObj (Over.mk f) := L.grpObjOverMk

  haveI : IsIntegral A := hA.isIntegral_of_field
  haveI hsm : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian A := {}
  have hX : ∀ x : A, IsDomain (A.presheaf.stalk x) ∧ IsIntegrallyClosed (A.presheaf.stalk x) := by
    have e : Γ(Spec (CommRingCat.of k), ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    have hF : IsField Γ(Spec (CommRingCat.of k), ⊤) := e.toMulEquiv.isField (Field.toIsField k)
    letI : Field Γ(Spec (CommRingCat.of k), ⊤) := hF.toField
    exact AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f

  set S : Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) :=
    {x | ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f,
      Scheme.Modules.pullbackSection z.left θ = 0 ↔ Scheme.Modules.pullbackSection (z * x).left θ = 0} with hSdef
  set D : Set A := ((Scheme.Modules.zeroSchemeIdeal θ).support : Set A) with hDdef
  have hDc : IsClosed D := by rw [hDdef]; exact (Scheme.Modules.zeroSchemeIdeal θ).support.isClosed

  have hpre : ∀ x ∈ S, (rt (Over.mk f) x).left.base ⁻¹' D = D := by
    intro x hx
    rw [hDdef]
    refine AlgebraicGeometry.Scheme.Modules.IsInvertible.preimage_support_zeroSchemeIdeal_eq_of_forall_pullbackSection_eq_zero_iff_comp
      f h𝓜 θ (rt (Over.mk f) x).left ?_
    intro z hz
    let z' : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f := Over.homMk z (by simpa using hz)
    have h2 := hx z'
    rw [mul_left f z' x] at h2
    exact h2

  set Comp : Set (Set A) := {C | Maximal (fun C' : Set A => IsIrreducible C' ∧ C' ⊆ D) C} with hCompdef
  have hCompfin : Comp.Finite := by rw [hCompdef]; exact finite_maximal_irreducible_subset hDc
  have hperm : ∀ x ∈ S, ∀ C ∈ Comp, (rt (Over.mk f) x).left.base '' C ∈ Comp := by
    intro x hx C hC
    rw [hCompdef] at hC ⊢
    have heq : ((Scheme.homeoOfIso (TIso f x)) : A → A) = (rt (Over.mk f) x).left.base := by
      funext a; rfl
    have hm := maximal_image (Scheme.homeoOfIso (TIso f x)) (D := D) (by rw [heq]; exact hpre x hx) hC
    rwa [heq] at hm

  by_contra hinf
  haveI : Infinite S := Set.infinite_coe_iff.mpr hinf
  haveI : Finite Comp := hCompfin.to_subtype
  let Φ : S → (Comp → Comp) := fun x C => ⟨(rt (Over.mk f) x.1).left.base '' C.1, hperm x.1 x.2 C.1 C.2⟩
  obtain ⟨π, hπ⟩ := Finite.exists_infinite_fiber Φ
  obtain ⟨x₀, hx₀⟩ := (Set.infinite_coe_iff.mp hπ).nonempty
  haveI : Finite (kernelPts f L 𝓜) := hK.to_subtype

  have key : ∀ x : S, Φ x = π → overHomToSchemeHomOver (x.1 * x₀.1⁻¹) ∈ kernelPts f L 𝓜 := by
    intro x hxπ
    have hcomp : ∀ (g h : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk f) (C : Set A),
        (rt (Over.mk f) (g * h)).left.base '' C = (rt (Over.mk f) h).left.base '' ((rt (Over.mk f) g).left.base '' C) := by
      intro g h C
      rw [left_rt_mul, Set.image_image]
      congr 1
    have hfix : ∀ C : Set A,
        Maximal (fun C' : Set A => IsIrreducible C' ∧ C' ⊆ (Scheme.Modules.zeroSchemeIdeal θ).support) C →
          (TIso f (x.1 * x₀.1⁻¹)).hom.base '' C = C := by
      intro C hC
      have hC' : C ∈ Comp := by rw [hCompdef, hDdef]; exact hC
      have h1 : (rt (Over.mk f) x.1).left.base '' C = (rt (Over.mk f) x₀.1).left.base '' C := by
        have := congrFun (hxπ.trans (Set.mem_preimage.mp hx₀).symm) ⟨C, hC'⟩
        exact congrArg Subtype.val this
      rw [TIso_hom]
      erw [hcomp, h1, ← hcomp, mul_inv_cancel, left_rt_one]
      ext a
      constructor
      · rintro ⟨b, hb, rfl⟩; exact hb
      · intro ha; exact ⟨a, ha, rfl⟩
    obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_pullback_iso_of_forall_maximal_isIrreducible_image_eq
      hX h𝓜 θ hθ (TIso f (x.1 * x₀.1⁻¹)) hfix
    rw [AlgebraicGeometry.Polarisation.mem_kernelPts_iff_nonempty_pullback_translate_iso, ← left_rt_eq_translate]
    exact ⟨e⟩
  have hfin : Finite (Φ ⁻¹' {π}) := by
    refine Finite.of_injective
      (fun x : Φ ⁻¹' {π} => (⟨overHomToSchemeHomOver (x.1.1 * x₀.1⁻¹), key x.1 x.2⟩ : kernelPts f L 𝓜)) ?_
    intro x y hxy
    have h1 : overHomToSchemeHomOver (x.1.1 * x₀.1⁻¹) = overHomToSchemeHomOver (y.1.1 * x₀.1⁻¹) :=
      congrArg Subtype.val hxy
    have h2 := congrArg schemeHomOverToOverHom h1
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver] at h2
    exact Subtype.ext (Subtype.ext (mul_right_cancel h2))
  exact @not_finite _ hπ hfin

end S_AlgebraicGeometry_Polarisation_finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_finite_setOf_forall_pullbackSection_eq_zero_iff_of_finite_kernelPts (solution)
