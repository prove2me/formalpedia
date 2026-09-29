-- Prove2me | solution 1 for AlgebraicGeometry.exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/29da3f32-c5d7-5000-be5e-5a40adef2e03

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace ChartPresentation

theorem appLE_top {X Y : Scheme.{u}} (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) : f.appLE ⊤ ⊤ e = f.appTop :=
  (Scheme.Hom.app_eq_appLE f).symm

theorem isAffineOpen_V
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    {A : Type u} [CommRing A] (φ : R →+* A) :
    IsAffineOpen ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
  letI : Algebra R A := φ.toAlgebra
  haveI : IsAffine (pullback (Spec.map (CommRingCat.ofHom (algebraMap R C))) (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :=
    IsAffine.of_isIso (pullbackSpecIso R C A).hom
  have hφ : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl
  haveI : IsAffine (pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom φ))) :=
    IsAffine.of_isIso (pullback.congrHom hι hφ).hom
  haveI : IsAffine (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
    IsAffine.of_isIso (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) ι).hom
  have h := isAffineOpen_opensRange (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ))))
  rwa [Scheme.Hom.opensRange_pullbackSnd, ← Scheme.Hom.image_top_eq_opensRange] at h

theorem closure_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    {A : Type u} [CommRing A] (φ : R →+* A) :
    Subring.closure (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) = ⊤ := by
  classical
  letI : Algebra R A := φ.toAlgebra
  have hcond : (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ ι = (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) := pullback.condition
  have hφ : (Spec.map (CommRingCat.ofHom φ)) = Spec.map (CommRingCat.ofHom (algebraMap R A)) := rfl

  let E : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≅ Spec (.of (TensorProduct R C A)) :=
    pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom φ)) ι ≪≫ pullback.congrHom hι hφ ≪≫ pullbackSpecIso R C A
  have hE1 : E.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* (TensorProduct R C A))) = (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_fst, pullback.congrHom_hom,
      pullback.lift_fst, Category.comp_id, pullbackRightPullbackFstIso_hom_fst]
  have hE2 : E.hom ≫ Spec.map (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A)))) = (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) := by
    simp only [E, Iso.trans_hom, Category.assoc, pullbackSpecIso_hom_snd, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id, pullbackRightPullbackFstIso_hom_snd]

  let Λ : (TensorProduct R C A) →+* Γ((pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))), ⊤) :=
    E.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of (TensorProduct R C A))).inv.hom
  have hΛsurj : Function.Surjective Λ := by
    intro y
    refine ⟨(Scheme.ΓSpecIso (.of (TensorProduct R C A))).hom.hom (E.inv.appTop.hom y), ?_⟩
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((Scheme.ΓSpecIso _).hom.hom (E.inv.appTop.hom y))) = y
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, E.hom_inv_id]
    simp
  have hΛC : ∀ b : C, Λ (b ⊗ₜ[R] 1) = (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b) := by
    intro b
    have h1 := CommRingCat.hom_ext_iff.mp (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : C →+* (TensorProduct R C A))))
    have h2 := RingHom.congr_fun h1 b
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom (Algebra.TensorProduct.includeLeftRingHom b)) = _
    erw [h2]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hE1]
  have hΛA : ∀ a : A, Λ (1 ⊗ₜ[R] a) = ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a) := by
    intro a
    have h1 := CommRingCat.hom_ext_iff.mp (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A)))))
    have h2 := RingHom.congr_fun h1 a
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    change E.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom ((RingHomClass.toRingHom (Algebra.TensorProduct.includeRight : A →ₐ[R] (TensorProduct R C A))) a)) = _
    erw [h2]
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hE2]

  have hgenP : ∀ y : Γ((pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))), ⊤), y ∈ Subring.closure (Set.range (fun b : C => (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b)) ∪
       Set.range (fun a : A => ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a))) := by
    intro y
    obtain ⟨t, rfl⟩ := hΛsurj y
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b a =>
        rw [show b ⊗ₜ[R] a = (b ⊗ₜ[R] (1 : A)) * ((1 : C) ⊗ₜ[R] a) by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, hΛC, hΛA]
        exact mul_mem (Subring.subset_closure (Or.inl ⟨b, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, rfl⟩))
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

  have hVg : (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ''ᵁ ⊤ = ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.image_top_eq_opensRange]
  have hle : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ⁻¹ᵁ ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) := by
    rw [← hVg, Scheme.Hom.preimage_image_eq]
  have hΨinj : Function.Injective ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom := by
    have hΨ' : (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle = (pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (eqToHom hVg).op ≫ ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appIso ⊤).hom := by
      rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE']
    rw [hΨ']
    exact (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.mapIso (eqToIso hVg).op ≪≫ (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appIso ⊤).commRingCatIsoToRingEquiv).injective

  have hΨC : ∀ b : C, ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom (((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) =
      (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b) := by
    intro b
    have e1 : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ⁻¹ᵁ (ι ''ᵁ ⊤) := hle
    rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ hle]

    have e2 : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ ((pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ ι) ⁻¹ᵁ (ι ''ᵁ ⊤) := by rw [hcond]; exact e1
    have step2 : ∀ (m m' : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ⟶ X) (hm : m = m') (e : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ m ⁻¹ᵁ (ι ''ᵁ ⊤)) (e' : (⊤ : (pullback ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).Opens) ≤ m' ⁻¹ᵁ (ι ''ᵁ ⊤)),
        m.appLE (ι ''ᵁ ⊤) ⊤ e = m'.appLE (ι ''ᵁ ⊤) ⊤ e' := by
      intro m m' hm e e'; subst hm; rfl
    rw [step2 _ _ hcond.symm _ e2, ← Scheme.Hom.appLE_comp_appLE (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ι (ι ''ᵁ ⊤) ⊤ ⊤ (by rw [Scheme.Hom.preimage_image_eq]) le_top,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply (ι.appIso ⊤).inv, Scheme.Hom.appIso_inv_appLE]
    simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply, appLE_top]
  have hΨA : ∀ a : A, ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE (le_top : ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ≤ ⊤)).op).hom ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) =
      ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a) := by
    intro a
    rw [← CommRingCat.comp_apply ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map _), Scheme.Hom.map_appLE]
    change ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop ≫ (pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ⊤ ⊤ _).hom _ = _
    rw [← appLE_top (pullback.snd f (Spec.map (CommRingCat.ofHom φ))) le_top, Scheme.Hom.appLE_comp_appLE, appLE_top]

  rw [eq_top_iff]
  rintro x -
  have hx := hgenP (((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom x)
  have hsub : Subring.closure (Set.range (fun b : C => (pullback.fst ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of C)).inv b)) ∪
       Set.range (fun a : A => ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) ≫ (pullback.snd f (Spec.map (CommRingCat.ofHom φ)))).appTop.hom ((Scheme.ΓSpecIso (.of A)).inv a))) ≤
      (Subring.closure  (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))))).map ((pullback.snd ι (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).appLE ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤)) ⊤ hle).hom := by
    rw [Subring.closure_le]
    rintro y (⟨b, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨_, Subring.subset_closure (Or.inl ⟨b, rfl⟩), hΨC b⟩
    · exact ⟨_, Subring.subset_closure (Or.inr ⟨a, rfl⟩), hΨA a⟩
  obtain ⟨x', hx', hxx'⟩ := hsub hx
  exact hΨinj hxx' ▸ hx'

end ChartPresentation

open ChartPresentation in
set_option maxHeartbeats 1600000 in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (C : Type u) [CommRing C] [Algebra R C] (ι : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion ι]
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R C)))
    {A : Type u} [CommRing A] (φ : R →+* A)
    (z : ↥(pullback f (Spec.map (CommRingCat.ofHom φ))))
    (hz : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))).base z ∈ ι ''ᵁ ⊤)
    (U : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (hzU : z ∈ U)
    (s : Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), U)) :
    ∃ (W : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens) (_ : z ∈ W) (hWU : W ≤ U)
      (hWV : W ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤))
      (σ τ : Γ(pullback f (Spec.map (CommRingCat.ofHom φ)), (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤))),
      σ ∈ Subring.closure
          (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
      τ ∈ Subring.closure
          (Set.range (fun b : C => ((pullback.fst f (Spec.map (CommRingCat.ofHom φ))).app (ι ''ᵁ ⊤)).hom
              ((ι.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of C)).inv b))) ∪
           Set.range (fun a : A => ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map
              (homOfLE (le_top : (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) ≤ ⊤)).op).hom
              ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) ∧
      IsUnit (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ) ∧
      ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWU).op).hom s *
          ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom τ =
        ((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hWV).op).hom σ := by
  classical

  have hV := isAffineOpen_V f C ι hι φ
  set V : (pullback f (Spec.map (CommRingCat.ofHom φ))).Opens := (pullback.fst f (Spec.map (CommRingCat.ofHom φ))) ⁻¹ᵁ (ι ''ᵁ ⊤) with hVdef
  have hzV : z ∈ V := hz

  obtain ⟨r, hrU, hzr⟩ := hV.exists_basicOpen_le ⟨z, hzU⟩ hzV
  have hWV : (pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r ≤ V := (pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen_le r

  haveI := hV.isLocalization_basicOpen r
  obtain ⟨⟨σ, ⟨_, n, rfl⟩⟩, hst⟩ :=
    IsLocalization.surj (Submonoid.powers r) (((pullback f (Spec.map (CommRingCat.ofHom φ))).presheaf.map (homOfLE hrU).op).hom s)
  have hgen := closure_eq_top f C ι hι φ
  refine ⟨(pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r, hzr, hrU, hWV, σ, r ^ n, ?_, ?_, ?_, ?_⟩
  · rw [hgen]; exact Subring.mem_top _
  · rw [hgen]; exact Subring.mem_top _
  · rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Γ((pullback f (Spec.map (CommRingCat.ofHom φ))), (pullback f (Spec.map (CommRingCat.ofHom φ))).basicOpen r)) r).pow n
  · exact hst

end S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections
end P2MW
export P2MW.S_AlgebraicGeometry_exists_opens_restrict_mul_eq_restrict_of_mem_closure_chart_sections (solution)
