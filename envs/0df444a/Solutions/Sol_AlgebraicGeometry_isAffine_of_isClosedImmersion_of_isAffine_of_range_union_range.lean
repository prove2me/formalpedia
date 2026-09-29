-- Prove2me | solution 1 for AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/85345dc8-eda8-51cb-a3e4-103ae159987f

import Mathlib
import Theorems.Thm_Ideal_injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Surjective Spec.map_comp_assoc basicOpen_eq_bot_iff Scheme.Hom isAffine_of_isAffineOpen_basicOpen iSup_affineOpens_eq_top Scheme.Pullback.range_fst IsAffine Scheme.preimage_basicOpen Scheme.Hom.support_ker IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.basicOpen_zero Scheme.Hom.comp_appTop Scheme.Pullback.range_snd IsClosedImmersion IsReduced Scheme.mem_zeroLocus_iff exists_isAffineOpen_mem_and_subset isAffineOpen_top Scheme.basicOpen_mul IsAffineOpen Scheme.Hom.ker_apply Scheme.toSpecΓ_preimage_basicOpen Scheme.IdealSheafData.mem_support_iff_of_mem toSpecΓ IsClosedImmersion.isAffine_surjective_of_isAffine Scheme.IdealSheafData Scheme.isoSpec_inv_toSpecΓ Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app"
p2m_open "AlgebraicGeometry"

namespace UnionAffine

theorem exists_basicOpen_of_isClosed_of_notMem {Z : Scheme.{u}} [IsAffine Z]
    (C : Set Z) (hC : IsClosed C) (z : Z) (hz : z ∉ C) :
    ∃ a : Γ(Z, ⊤), z ∈ Z.basicOpen a ∧ ∀ c ∈ C, c ∉ Z.basicOpen a := by
  obtain ⟨I, rfl⟩ := (Z.eq_zeroLocus_of_isClosed_of_isAffine C).mp hC
  rw [Scheme.mem_zeroLocus_iff] at hz
  push Not at hz
  obtain ⟨a, haI, hza⟩ := hz
  exact ⟨a, hza, fun c hc => (Scheme.mem_zeroLocus_iff _ _ _).mp hc a haI⟩

theorem exists_appTop_eq_zero_and_mem_basicOpen {W Z : Scheme.{u}} [IsAffine Z] (ι : W ⟶ Z)
    [IsClosedImmersion ι] (z : Z) (hz : z ∉ Set.range ι.base) :
    ∃ a : Γ(Z, ⊤), ι.appTop a = 0 ∧ z ∈ Z.basicOpen a := by
  have hz' : z ∉ (ι.ker.support : Set Z) := by
    rw [Scheme.Hom.support_ker, ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact hz
  rw [SetLike.mem_coe, Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨⊤, isAffineOpen_top Z⟩) (Set.mem_univ z),
    Scheme.Hom.ker_apply, Scheme.mem_zeroLocus_iff] at hz'
  push Not at hz'
  obtain ⟨a, ha, hza⟩ := hz'
  exact ⟨a, (RingHom.mem_ker).mp ha, hza⟩

theorem exists_forall_mem_basicOpen_iff {Z : Scheme.{u}} [IsAffine Z] (p : PrimeSpectrum Γ(Z, ⊤)) :
    ∃ z : Z, ∀ a : Γ(Z, ⊤), z ∈ Z.basicOpen a ↔ a ∉ p.asIdeal := by
  refine ⟨Z.isoSpec.inv.base p, fun a => ?_⟩
  have hp : Z.toSpecΓ.base (Z.isoSpec.inv.base p) = p := by
    change (Z.isoSpec.inv ≫ Z.toSpecΓ).base p = p
    rw [Scheme.isoSpec_inv_toSpecΓ]
    rfl
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  change Z.toSpecΓ.base (Z.isoSpec.inv.base p) ∈ PrimeSpectrum.basicOpen a ↔ _
  rw [hp]
  exact PrimeSpectrum.mem_basicOpen a p

theorem eq_zero_of_app_eq_zero {X Z₁ Z₂ : Scheme.{u}} [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) {V : X.Opens} (s : Γ(X, V))
    (h₁ : i₁.app V s = 0) (h₂ : i₂.app V s = 0) : s = 0 := by
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hx' : x ∈ Set.range i₁.base ∪ Set.range i₂.base := hcov.symm ▸ Set.mem_univ x
  rcases hx' with ⟨z, rfl⟩ | ⟨z, rfl⟩
  · have hz : z ∈ i₁ ⁻¹ᵁ X.basicOpen s := hx
    rw [Scheme.preimage_basicOpen, h₁, Scheme.basicOpen_zero] at hz
    exact hz
  · have hz : z ∈ i₂ ⁻¹ᵁ X.basicOpen s := hx
    rw [Scheme.preimage_basicOpen, h₂, Scheme.basicOpen_zero] at hz
    exact hz

theorem ker_inf_ker_eq_bot {X Z₁ Z₂ : Scheme.{u}} [IsReduced X] (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) (V : X.Opens) :
    RingHom.ker (i₁.app V).hom ⊓ RingHom.ker (i₂.app V).hom = ⊥ := by
  rw [eq_bot_iff]
  rintro s ⟨h₁, h₂⟩
  exact eq_zero_of_app_eq_zero i₁ i₂ hcov s h₁ h₂

theorem exists_ringHom_comp_eq_of_surjective {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (π : A →+* B) (hπ : Function.Surjective π) (g : A →+* C) (hle : RingHom.ker π ≤ RingHom.ker g) :
    ∃ ρ : B →+* C, ρ.comp π = g := by
  refine ⟨(Ideal.Quotient.lift (RingHom.ker π) g fun a ha => hle ha).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom, ?_⟩
  ext a
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  have : (RingHom.quotientKerEquivOfSurjective hπ).symm (π a) = Ideal.Quotient.mk (RingHom.ker π) a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  rw [this, Ideal.Quotient.lift_mk]

theorem app_map_apply {X Z : Scheme.{u}} (i : Z ⟶ X) {U V : X.Opens} (ι : V ⟶ U) (s : Γ(X, U)) :
    i.app V (X.presheaf.map ι.op s) =
      Z.presheaf.map ((Opens.map i.base).map ι).op (i.app U s) := by
  rw [← CommRingCat.comp_apply, i.naturality]
  rfl

theorem appTop_SpecMap_comp_fromSpec {Z : Scheme.{u}} {V : Z.Opens} (hV : IsAffineOpen V)
    {R : CommRingCat.{u}} (φ : Γ(Z, V) ⟶ R) (a : Γ(Z, ⊤)) :
    (Spec.map φ ≫ hV.fromSpec).appTop a =
      (Scheme.ΓSpecIso R).inv (φ (Z.presheaf.map (homOfLE le_top).op a)) := by
  have nat := congrArg (fun ψ => ψ (Z.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op a))
    (Scheme.ΓSpecIso_inv_naturality φ)
  simp only [CommRingCat.comp_apply] at nat
  rw [nat, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  change (Spec.map φ).appTop (hV.fromSpec.app ⊤ a) = _
  rw [hV.fromSpec_app_of_le ⊤ le_top, CommRingCat.comp_apply, CommRingCat.comp_apply]
  congr 1

section Glue

variable {X Z₁ Z₂ : Scheme.{0}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsReduced X]
  (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)

omit [IsReduced X] in

theorem sub_mem_ker_sup_ker (U : X.Opens) (hU : IsAffineOpen U) (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂)
    (t₁ t₂ : Γ(X, U))
    (ht₁ : i₁.app U t₁ = Z₁.presheaf.map (homOfLE le_top).op a₁)
    (ht₂ : i₂.app U t₂ = Z₂.presheaf.map (homOfLE le_top).op a₂) :
    t₁ - t₂ ∈ RingHom.ker (i₁.app U).hom ⊔ RingHom.ker (i₂.app U).hom := by
  set J : Ideal Γ(X, U) := RingHom.ker (i₁.app U).hom ⊔ RingHom.ker (i₂.app U).hom with hJ
  obtain ⟨ρ₁, hρ₁⟩ := exists_ringHom_comp_eq_of_surjective (i₁.app U).hom (i₁.app_surjective U hU)
    (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact le_sup_left)
  obtain ⟨ρ₂, hρ₂⟩ := exists_ringHom_comp_eq_of_surjective (i₂.app U).hom (i₂.app_surjective U hU)
    (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact le_sup_right)
  have hV₁ : IsAffineOpen (i₁ ⁻¹ᵁ U) := hU.preimage i₁
  have hV₂ : IsAffineOpen (i₂ ⁻¹ᵁ U) := hU.preimage i₂
  let Q : CommRingCat.{0} := CommRingCat.of (Γ(X, U) ⧸ J)
  let g₁ : Spec Q ⟶ Z₁ := Spec.map (CommRingCat.ofHom ρ₁) ≫ hV₁.fromSpec
  let g₂ : Spec Q ⟶ Z₂ := Spec.map (CommRingCat.ofHom ρ₂) ≫ hV₂.fromSpec
  have hπρ : i₁.appLE U (i₁ ⁻¹ᵁ U) le_rfl ≫ CommRingCat.ofHom ρ₁ =
      i₂.appLE U (i₂ ⁻¹ᵁ U) le_rfl ≫ CommRingCat.ofHom ρ₂ := by
    ext x
    rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.appLE_eq_app]
    change (ρ₁.comp (i₁.app U).hom) x = (ρ₂.comp (i₂.app U).hom) x
    rw [hρ₁, hρ₂]
  have comm : g₁ ≫ i₁ = g₂ ≫ i₂ := by
    simp only [g₁, g₂, Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec i₁ hU hV₁ le_rfl,
      ← IsAffineOpen.SpecMap_appLE_fromSpec i₂ hU hV₂ le_rfl,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hπρ]
  have e : g₁.appTop a₁ = g₂.appTop a₂ := by
    have := congrArg (fun y => (pullback.lift g₁ g₂ comm).appTop y) h
    simp only [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, pullback.lift_fst,
      pullback.lift_snd] at this
    exact this
  simp only [g₁, g₂, appTop_SpecMap_comp_fromSpec] at e
  have inj : Function.Injective (Scheme.ΓSpecIso Q).inv := (ConcreteCategory.bijective_of_isIso _).1
  have e' := inj e
  change ρ₁ (Z₁.presheaf.map (homOfLE le_top).op a₁) = ρ₂ (Z₂.presheaf.map (homOfLE le_top).op a₂) at e'
  rw [← ht₁, ← ht₂] at e'
  change (ρ₁.comp (i₁.app U).hom) t₁ = (ρ₂.comp (i₂.app U).hom) t₂ at e'
  rw [hρ₁, hρ₂] at e'
  exact Ideal.Quotient.eq.mp e'

include hcov in

theorem exists_section_local (U : X.Opens) (hU : IsAffineOpen U) (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂) :
    ∃ s : Γ(X, U), i₁.app U s = Z₁.presheaf.map (homOfLE le_top).op a₁ ∧
      i₂.app U s = Z₂.presheaf.map (homOfLE le_top).op a₂ := by
  obtain ⟨t₁, ht₁⟩ := i₁.app_surjective U hU (Z₁.presheaf.map (homOfLE le_top).op a₁)
  obtain ⟨t₂, ht₂⟩ := i₂.app_surjective U hU (Z₂.presheaf.map (homOfLE le_top).op a₂)
  have key := sub_mem_ker_sup_ker i₁ i₂ U hU a₁ a₂ h t₁ t₂ ht₁ ht₂
  obtain ⟨-, hF1⟩ := Ideal.injective_quotient_mk_prod_and_exists_of_factor_eq_of_inf_eq_bot
    Γ(X, U) (RingHom.ker (i₁.app U).hom) (RingHom.ker (i₂.app U).hom)
    (ker_inf_ker_eq_bot i₁ i₂ hcov U)
  obtain ⟨s, hs₁, hs₂⟩ := hF1 (Ideal.Quotient.mk _ t₁) (Ideal.Quotient.mk _ t₂) (by
    rw [Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]
    exact Ideal.Quotient.eq.mpr key)
  refine ⟨s, ?_, ?_⟩
  · rw [← ht₁]
    exact (RingHom.sub_mem_ker_iff _).mp (Ideal.Quotient.eq.mp hs₁)
  · rw [← ht₂]
    exact (RingHom.sub_mem_ker_iff _).mp (Ideal.Quotient.eq.mp hs₂)

include hcov in

theorem exists_section (a₁ : Γ(Z₁, ⊤)) (a₂ : Γ(Z₂, ⊤))
    (h : (pullback.fst i₁ i₂).appTop a₁ = (pullback.snd i₁ i₂).appTop a₂) :
    ∃ s : Γ(X, ⊤), i₁.appTop s = a₁ ∧ i₂.appTop s = a₂ := by
  choose sf hsf₁ hsf₂ using fun U : X.affineOpens => exists_section_local i₁ i₂ hcov U.1 U.2 a₁ a₂ h
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf
      (fun U : X.affineOpens => (U : X.Opens)) sf := by
    intro U V
    change X.presheaf.map (Opens.infLELeft U.1 V.1).op (sf U) =
      X.presheaf.map (Opens.infLERight U.1 V.1).op (sf V)
    rw [← sub_eq_zero]
    apply eq_zero_of_app_eq_zero i₁ i₂ hcov
    · rw [map_sub, sub_eq_zero, app_map_apply, app_map_apply, hsf₁, hsf₁, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
    · rw [map_sub, sub_eq_zero, app_map_apply, app_map_apply, hsf₂, hsf₂, ← CommRingCat.comp_apply,
        ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
      rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun U : X.affineOpens => (U : X.Opens)) ⊤
    (fun U => homOfLE le_top) (by rw [iSup_affineOpens_eq_top X]) sf hcompat
  have cover : ∀ {Z : Scheme.{0}} (i : Z ⟶ X),
      (⊤ : Z.Opens) ≤ ⨆ U : X.affineOpens, i ⁻¹ᵁ (U : X.Opens) := by
    intro Z i z _
    rw [Opens.mem_iSup]
    obtain ⟨U, hU, hzU, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := X) (x := i.base z) (U := ⊤) trivial
    exact ⟨⟨U, hU⟩, hzU⟩
  refine ⟨s, ?_, ?_⟩
  · refine Z₁.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => i₁ ⁻¹ᵁ (U : X.Opens)) ⊤
      (fun U => homOfLE le_top) (cover i₁) _ _ fun U => ?_
    change Z₁.presheaf.map (homOfLE le_top).op (i₁.app ⊤ s) =
      Z₁.presheaf.map (homOfLE le_top).op a₁
    rw [← hsf₁ U, ← hs U]
    change _ = i₁.app U.1 (X.presheaf.map (homOfLE le_top).op s)
    rw [app_map_apply]
    rfl
  · refine Z₂.sheaf.eq_of_locally_eq' (fun U : X.affineOpens => i₂ ⁻¹ᵁ (U : X.Opens)) ⊤
      (fun U => homOfLE le_top) (cover i₂) _ _ fun U => ?_
    change Z₂.presheaf.map (homOfLE le_top).op (i₂.app ⊤ s) =
      Z₂.presheaf.map (homOfLE le_top).op a₂
    rw [← hsf₂ U, ← hs U]
    change _ = i₂.app U.1 (X.presheaf.map (homOfLE le_top).op s)
    rw [app_map_apply]
    rfl

include hcov in
theorem appTop_surjective_left [IsAffine Z₂] : Function.Surjective i₁.appTop := by
  intro a₁
  obtain ⟨a₂, ha₂⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.snd i₁ i₂)).2
    ((pullback.fst i₁ i₂).appTop a₁)
  obtain ⟨s, hs, -⟩ := exists_section i₁ i₂ hcov a₁ a₂ ha₂.symm
  exact ⟨s, hs⟩

include hcov in
theorem appTop_surjective_right [IsAffine Z₁] : Function.Surjective i₂.appTop := by
  intro a₂
  obtain ⟨a₁, ha₁⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine (pullback.fst i₁ i₂)).2
    ((pullback.snd i₁ i₂).appTop a₂)
  obtain ⟨s, -, hs⟩ := exists_section i₁ i₂ hcov a₁ a₂ ha₁
  exact ⟨s, hs⟩

include hcov in
theorem exists_appTop_eq_zero_left [IsAffine Z₁] (w : Z₁)
    (hw : w ∉ i₁.base ⁻¹' Set.range i₂.base) :
    ∃ f : Γ(X, ⊤), i₂.appTop f = 0 ∧ w ∈ Z₁.basicOpen (i₁.appTop f) := by
  rw [← Scheme.Pullback.range_fst] at hw
  obtain ⟨a, ha, hwa⟩ := exists_appTop_eq_zero_and_mem_basicOpen (pullback.fst i₁ i₂) w hw
  obtain ⟨f, hf₁, hf₂⟩ := exists_section i₁ i₂ hcov a 0 (by rw [ha, map_zero])
  exact ⟨f, hf₂, hf₁ ▸ hwa⟩

include hcov in
theorem exists_appTop_eq_zero_right [IsAffine Z₂] (w : Z₂)
    (hw : w ∉ i₂.base ⁻¹' Set.range i₁.base) :
    ∃ f : Γ(X, ⊤), i₁.appTop f = 0 ∧ w ∈ Z₂.basicOpen (i₂.appTop f) := by
  rw [← Scheme.Pullback.range_snd] at hw
  obtain ⟨a, ha, hwa⟩ := exists_appTop_eq_zero_and_mem_basicOpen (pullback.snd i₁ i₂) w hw
  obtain ⟨f, hf₁, hf₂⟩ := exists_section i₁ i₂ hcov 0 a (by rw [ha, map_zero])
  exact ⟨f, hf₁, hf₂ ▸ hwa⟩

end Glue

theorem exists_basicOpen_oneSided {X Z Z' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X) [IsAffine Z]
    (hcov : ∀ x : X, x ∈ Set.range i.base ∨ x ∈ Set.range i'.base)
    (hsurj : Function.Surjective i.appTop)
    (hker : ∀ w : Z', w ∉ i'.base ⁻¹' Set.range i.base →
      ∃ f : Γ(X, ⊤), i.appTop f = 0 ∧ w ∈ Z'.basicOpen (i'.appTop f))
    (x : X) (U : X.Opens) (hxU : x ∈ U) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ ∀ z : Z, i.base z ∈ X.basicOpen f → i.base z ∈ U := by
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z, rfl⟩ := hx
    obtain ⟨a, hza, hCa⟩ := exists_basicOpen_of_isClosed_of_notMem ((i ⁻¹ᵁ U : Set Z)ᶜ)
      (i ⁻¹ᵁ U).isOpen.isClosed_compl z (by simpa using hxU)
    obtain ⟨f, rfl⟩ := hsurj a
    refine ⟨f, ?_, fun z' hz' => ?_⟩
    · have : z ∈ i ⁻¹ᵁ X.basicOpen f := by rwa [Scheme.preimage_basicOpen]
      exact this
    · have hz'' : z' ∈ i ⁻¹ᵁ X.basicOpen f := hz'
      rw [Scheme.preimage_basicOpen] at hz''
      have := hCa z'
      simp only [Set.mem_compl_iff, SetLike.mem_coe] at this
      by_contra hU
      exact this hU hz''
  · obtain ⟨w, rfl⟩ := (hcov x).resolve_left hx
    obtain ⟨f, hf0, hwf⟩ := hker w hx
    refine ⟨f, ?_, fun z hz => ?_⟩
    · have : w ∈ i' ⁻¹ᵁ X.basicOpen f := by rwa [Scheme.preimage_basicOpen]
      exact this
    · have hz' : z ∈ i ⁻¹ᵁ X.basicOpen f := hz
      rw [Scheme.preimage_basicOpen] at hz'
      change z ∈ Z.basicOpen (i.appTop f) at hz'
      rw [hf0, Scheme.basicOpen_zero] at hz'
      exact hz'.elim

section Cover

variable {X Z₁ Z₂ : Scheme.{0}} (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
  [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsAffine Z₁] [IsAffine Z₂] [IsReduced X]
  (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ)

include hcov in

theorem exists_mem_basicOpen_and_isAffineOpen (x : X) :
    ∃ f : Γ(X, ⊤), x ∈ X.basicOpen f ∧ IsAffineOpen (X.basicOpen f) := by
  have hcov' : ∀ x : X, x ∈ Set.range i₁.base ∨ x ∈ Set.range i₂.base := fun x =>
    (Set.mem_union _ _ _).mp (hcov.symm ▸ Set.mem_univ x)
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨f₁, hx₁, hU₁⟩ := exists_basicOpen_oneSided i₁ i₂ hcov'
    (appTop_surjective_left i₁ i₂ hcov) (exists_appTop_eq_zero_right i₁ i₂ hcov) x U hxU
  obtain ⟨f₂, hx₂, hU₂⟩ := exists_basicOpen_oneSided i₂ i₁ (fun x => (hcov' x).symm)
    (appTop_surjective_right i₁ i₂ hcov) (exists_appTop_eq_zero_left i₁ i₂ hcov) x U hxU
  refine ⟨f₁ * f₂, ?_, ?_⟩
  · rw [Scheme.basicOpen_mul]; exact ⟨hx₁, hx₂⟩
  · have hle : X.basicOpen (f₁ * f₂) ≤ U := by
      intro y hy
      rw [Scheme.basicOpen_mul] at hy
      rcases hcov' y with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact hU₁ z hy.1
      · exact hU₂ z hy.2
    have : X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (f₁ * f₂)) =
        X.basicOpen (f₁ * f₂) := by
      rw [Scheme.basicOpen_res]
      exact inf_eq_right.mpr hle
    rw [← this]
    exact hU.basicOpen _

end Cover

theorem not_subset_of_ker_le {X Z : Scheme.{u}} [IsAffine Z] (i : Z ⟶ X)
    (hsurj : Function.Surjective i.appTop) (𝔪 : Ideal Γ(X, ⊤)) [h𝔪 : 𝔪.IsMaximal]
    (hker : RingHom.ker i.appTop.hom ≤ 𝔪) (S : Set Γ(X, ⊤))
    (hL : ∀ z : Z, ∃ f ∈ S, i.base z ∈ X.basicOpen f) : ¬ S ⊆ 𝔪 := by
  intro hS
  have hne : 𝔪.map i.appTop.hom ≠ ⊤ := by
    intro htop
    have := congr_arg (Ideal.comap i.appTop.hom) htop
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker] at this
    exact h𝔪.ne_top this
  obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨z, hz⟩ := exists_forall_mem_basicOpen_iff (Z := Z) ⟨𝔭, h𝔭.isPrime⟩
  obtain ⟨f, hfS, hzf⟩ := hL z
  have h1 : i.appTop f ∉ 𝔭 := by
    rw [← hz]
    have : z ∈ i ⁻¹ᵁ X.basicOpen f := hzf
    rwa [Scheme.preimage_basicOpen] at this
  exact h1 (hle (Ideal.mem_map_of_mem _ (hS hfS)))

end UnionAffine

end AlgebraicGeometry

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.basicOpen_res Surjective Spec.map_comp_assoc basicOpen_eq_bot_iff Scheme.Hom isAffine_of_isAffineOpen_basicOpen iSup_affineOpens_eq_top Scheme.Pullback.range_fst IsAffine Scheme.preimage_basicOpen Scheme.Hom.support_ker IsAffineOpen.SpecMap_appLE_fromSpec Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme Scheme.basicOpen_zero Scheme.Hom.comp_appTop Scheme.Pullback.range_snd IsClosedImmersion IsReduced Scheme.mem_zeroLocus_iff exists_isAffineOpen_mem_and_subset isAffineOpen_top Scheme.basicOpen_mul IsAffineOpen Scheme.Hom.ker_apply Scheme.toSpecΓ_preimage_basicOpen Scheme.IdealSheafData.mem_support_iff_of_mem toSpecΓ IsClosedImmersion.isAffine_surjective_of_isAffine Scheme.IdealSheafData Scheme.isoSpec_inv_toSpecΓ Scheme.ΓSpecIso Scheme.Hom.appLE_eq_app" namespace UnionAffine end AlgebraicGeometry.UnionAffine
p2m_open_scoped "AlgebraicGeometry" in
open AlgebraicGeometry.UnionAffine in

theorem AlgebraicGeometry.UnionAffine.isAffine_of_isClosedImmersion_of_range_union_range
    (X Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (h₁ : IsClosedImmersion i₁) (h₂ : IsClosedImmersion i₂)
    (hZ₁ : IsAffine Z₁) (hZ₂ : IsAffine Z₂)
    (hred : IsReduced X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X := by
  let S : Set Γ(X, ⊤) := {f | IsAffineOpen (X.basicOpen f)}
  refine isAffine_of_isAffineOpen_basicOpen S ?_ (fun f hf => hf)
  by_contra hne
  obtain ⟨𝔪, h𝔪, hS𝔪⟩ := Ideal.exists_le_maximal _ hne
  have hS : S ⊆ 𝔪 := fun f hf => hS𝔪 (Ideal.subset_span hf)
  have hL := exists_mem_basicOpen_and_isAffineOpen i₁ i₂ hcov
  have hbot := ker_inf_ker_eq_bot i₁ i₂ hcov ⊤
  have hI : RingHom.ker (i₁.appTop).hom ≤ 𝔪 ∨ RingHom.ker (i₂.appTop).hom ≤ 𝔪 := by
    refine h𝔪.isPrime.mul_le.mp (le_trans Ideal.mul_le_inf ?_)
    change RingHom.ker (i₁.app ⊤).hom ⊓ RingHom.ker (i₂.app ⊤).hom ≤ 𝔪
    rw [hbot]; exact bot_le
  rcases hI with hI | hI
  · exact not_subset_of_ker_le i₁ (appTop_surjective_left i₁ i₂ hcov) 𝔪 hI S
      (fun z => let ⟨f, hf, hfa⟩ := hL (i₁.base z); ⟨f, hfa, hf⟩) hS
  · exact not_subset_of_ker_le i₂ (appTop_surjective_right i₁ i₂ hcov) 𝔪 hI S
      (fun z => let ⟨f, hf, hfa⟩ := hL (i₂.base z); ⟨f, hfa, hf⟩) hS

theorem solution
    (X Z₁ Z₂ : Scheme.{0}) (i₁ : Z₁ ⟶ X) (i₂ : Z₂ ⟶ X)
    (h₁ : IsClosedImmersion i₁) (h₂ : IsClosedImmersion i₂)
    (hZ₁ : IsAffine Z₁) (hZ₂ : IsAffine Z₂)
    (hred : IsReduced X)
    (hcov : Set.range i₁.base ∪ Set.range i₂.base = Set.univ) :
    IsAffine X :=
  AlgebraicGeometry.UnionAffine.isAffine_of_isClosedImmersion_of_range_union_range
    X Z₁ Z₂ i₁ i₂ h₁ h₂ hZ₁ hZ₂ hred hcov

end S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range
end P2MW
export P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isAffine_of_range_union_range (solution)
