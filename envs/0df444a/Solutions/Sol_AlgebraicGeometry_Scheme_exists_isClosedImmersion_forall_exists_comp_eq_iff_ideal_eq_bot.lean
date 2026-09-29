-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9b1fbe07-c79c-5107-b0f2-3e8d49b9e6c2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

noncomputable section

namespace G0

variable (E : Scheme.{u})
  (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
  (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ)

def idealOf (U : E.affineOpens) : Ideal Γ(E, U) := I (Γ(E, U)) U.2.fromSpec

include hI in
theorem idealOf_map {U V : E.affineOpens} (h : V.1 ≤ U.1) :
    (idealOf E I U).map (E.presheaf.map (homOfLE h).op).hom = idealOf E I V := by
  unfold idealOf
  rw [← hI, CommRingCat.ofHom_hom, IsAffineOpen.map_fromSpec U.2 V.2 (homOfLE h).op]

def J : E.IdealSheafData where
  ideal U := idealOf E I U
  map_ideal_basicOpen U f := by
    have h := idealOf_map E I hI (U := U) (V := E.affineBasicOpen f) (E.basicOpen_le f)
    exact h

@[scoped simp] theorem J_ideal (U : E.affineOpens) : (J E I hI).ideal U = I (Γ(E, U)) U.2.fromSpec := rfl

section AffinePoints

variable (R : Type u) [CommRing R]

def ψV (V : (Spec (CommRingCat.of R)).affineOpens) : R →+* Γ(Spec (CommRingCat.of R), V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec (CommRingCat.of R)).presheaf.map (homOfLE le_top).op).hom

theorem fromSpec_eq_specMap_ψV (V : (Spec (CommRingCat.of R)).affineOpens) :
    V.2.fromSpec = Spec.map (CommRingCat.ofHom (ψV R V)) := by
  rw [ψV, CommRingCat.ofHom_hom, Spec.map_comp, ← IsAffineOpen.fromSpec_toSpecΓ, Category.assoc,
    ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]

end AffinePoints

variable {E}

include hI in

theorem exists_theta {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E)
    (U : E.affineOpens) (V : (Spec (CommRingCat.of R)).affineOpens) (hV : V.1 ≤ s ⁻¹ᵁ U.1) :
    ∃ θ : Γ(E, U) ⟶ Γ(Spec (CommRingCat.of R), V),
      Spec.map θ ≫ U.2.fromSpec = V.2.fromSpec ≫ s ∧
      (idealOf E I U).map θ.hom = (I R s).map (ψV R V) := by
  have hrange : Set.range (V.2.fromSpec ≫ s) ⊆ Set.range U.1.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hy : V.2.fromSpec y ∈ (V.1 : Set _) := by
      have : V.2.fromSpec y ∈ Set.range V.2.fromSpec := ⟨y, rfl⟩
      rwa [IsAffineOpen.range_fromSpec] at this
    exact hV hy
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (IsOpenImmersion.lift U.1.ι _ hrange ≫ U.2.isoSpec.hom)
  refine ⟨θ, ?_, ?_⟩
  · rw [hθ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι (hU := U.2), U.2.isoSpec.hom_inv_id_assoc, IsOpenImmersion.lift_fac]
  · have h1 := hI (Γ(E, U)) (Γ(Spec (CommRingCat.of R), V)) θ.hom U.2.fromSpec
    rw [CommRingCat.ofHom_hom] at h1
    have h2 := hI R (Γ(Spec (CommRingCat.of R), V)) (ψV R V) s
    rw [← fromSpec_eq_specMap_ψV] at h2
    unfold idealOf
    rw [← h1, ← h2]
    congr 1
    rw [hθ, Category.assoc, ← IsAffineOpen.isoSpec_inv_ι (hU := U.2), U.2.isoSpec.hom_inv_id_assoc, IsOpenImmersion.lift_fac]

theorem iSup_small_eq_top {R : Type u} [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E) :
    (⨆ V : {V : (Spec (CommRingCat.of R)).affineOpens // ∃ U : E.affineOpens, V.1 ≤ s ⁻¹ᵁ U.1}, V.1.1) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.isBasis_affineOpens)
    (TopologicalSpace.Opens.mem_top (s x))
  obtain ⟨V, hVaff, hxV, hVle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Spec (CommRingCat.of R)).isBasis_affineOpens) (show x ∈ s ⁻¹ᵁ U from hxU)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hVaff⟩, ⟨U, hU⟩, hVle⟩, hxV⟩

include hI in

theorem main : ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ := by
  refine ⟨(J E I hI).subscheme, (J E I hI).subschemeι, inferInstance, fun R _ s => ?_⟩

  let ι₀ := {V : (Spec (CommRingCat.of R)).affineOpens // ∃ U : E.affineOpens, V.1 ≤ s ⁻¹ᵁ U.1}
  have hU : ∀ V : ι₀, ∃ U : E.affineOpens, V.1.1 ≤ s ⁻¹ᵁ U.1 := fun V => V.2
  choose Uof hUof using hU
  have hloc : ∀ V : ι₀, ∃ θ : Γ(E, Uof V) ⟶ Γ(Spec (CommRingCat.of R), V.1),
      Spec.map θ ≫ (Uof V).2.fromSpec = V.1.2.fromSpec ≫ s ∧
      (idealOf E I (Uof V)).map θ.hom = (I R s).map (ψV R V.1) := fun V => exists_theta I hI s (Uof V) V.1 (hUof V)
  choose θ hθ₁ hθ₂ using hloc
  constructor
  ·
    rintro ⟨z, hz⟩
    have hlocal : ∀ V : ι₀, (I R s).map (ψV R V.1) = ⊥ := by
      intro V
      rw [← hθ₂]

      have hr : Set.range (V.1.2.fromSpec ≫ z) ⊆ Set.range ((J E I hI).subschemeCover.f (Uof V)) := by
        rintro _ ⟨y, rfl⟩
        rw [← Scheme.Hom.coe_opensRange, Scheme.IdealSheafData.opensRange_subschemeCover_map]
        show (J E I hI).subschemeι (z (V.1.2.fromSpec y)) ∈ ((Uof V) : E.Opens)
        rw [← Scheme.Hom.comp_apply z, hz]
        have hy : V.1.2.fromSpec y ∈ (V.1.1 : Set _) := by
          have : V.1.2.fromSpec y ∈ Set.range V.1.2.fromSpec := ⟨y, rfl⟩
          rwa [IsAffineOpen.range_fromSpec] at this
        exact hUof V hy
      obtain ⟨w, hw⟩ : ∃ w : Spec Γ(Spec (CommRingCat.of R), V.1) ⟶ Spec ((J E I hI).subschemeCover.X (Uof V)),
          w ≫ (J E I hI).subschemeCover.f (Uof V) = V.1.2.fromSpec ≫ z :=
        ⟨IsOpenImmersion.lift ((J E I hI).subschemeCover.f (Uof V)) (V.1.2.fromSpec ≫ z) hr,
          IsOpenImmersion.lift_fac ((J E I hI).subschemeCover.f (Uof V)) (V.1.2.fromSpec ≫ z) hr⟩
      obtain ⟨θ', hθ'⟩ := Spec.map_surjective w
      have e1 : (J E I hI).subschemeCover.f (Uof V) ≫ (J E I hI).subschemeι =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) ≫ (Uof V).2.fromSpec := by
        rw [Scheme.IdealSheafData.subschemeCover_map_subschemeι, Scheme.IdealSheafData.glueDataObjι_ι]
      have hcomp : w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) = Spec.map (θ V) := by
        rw [← cancel_mono (Uof V).2.fromSpec, Category.assoc]
        erw [← e1]
        rw [← Category.assoc, hw, Category.assoc, hz, hθ₁]
      rw [← hθ', ← Spec.map_comp] at hcomp
      have hfac := Spec.map_injective hcomp

      rw [← hfac, CommRingCat.hom_comp, ← Ideal.map_map]
      show ((idealOf E I (Uof V)).map (Ideal.Quotient.mk (idealOf E I (Uof V)))).map _ = ⊥
      rw [Ideal.map_quotient_self, Ideal.map_bot]

    rw [eq_bot_iff]
    intro x hx
    let σ : Γ(Spec (CommRingCat.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).inv x
    have hσ : σ = 0 := by
      apply TopCat.Sheaf.eq_of_locally_eq' (Spec (CommRingCat.of R)).sheaf (fun V : ι₀ => V.1.1) ⊤
        (fun V => homOfLE le_top) (by rw [iSup_small_eq_top])
      intro V
      erw [map_zero]
      have hm : ψV R V.1 x ∈ (I R s).map (ψV R V.1) := Ideal.mem_map_of_mem _ hx
      rw [hlocal V, Ideal.mem_bot] at hm
      exact hm
    have : x = (Scheme.ΓSpecIso (.of R)).hom σ := by
      show x = ((Scheme.ΓSpecIso (.of R)).inv ≫ (Scheme.ΓSpecIso (.of R)).hom) x
      rw [Iso.inv_hom_id]; rfl
    rw [this, hσ, map_zero]
    exact Ideal.zero_mem _
  ·
    intro hs
    have hker : ∀ (V : ι₀), ∀ a ∈ idealOf E I (Uof V), (θ V).hom a = 0 := by
      intro V a ha
      have h := hθ₂ V
      rw [hs, Ideal.map_bot, Ideal.map_eq_bot_iff_le_ker] at h
      exact h ha
    have e1 : ∀ V : ι₀, (J E I hI).subschemeCover.f (Uof V) ≫ (J E I hI).subschemeι =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V)))) ≫ (Uof V).2.fromSpec := by
      intro V
      rw [Scheme.IdealSheafData.subschemeCover_map_subschemeι, Scheme.IdealSheafData.glueDataObjι_ι]
    let zloc : ∀ V : ι₀, (V.1.1 : Scheme.{u}) ⟶ (J E I hI).subscheme := fun V =>
      V.1.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (θ V).hom (hker V))) ≫
        (J E I hI).subschemeCover.f (Uof V)
    have hzloc : ∀ V : ι₀, zloc V ≫ (J E I hI).subschemeι = V.1.1.ι ≫ s := by
      intro V
      simp only [zloc, Category.assoc]
      erw [e1 V]
      erw [← Spec.map_comp_assoc]
      have : CommRingCat.ofHom (Ideal.Quotient.mk ((J E I hI).ideal (Uof V))) ≫
          CommRingCat.ofHom (Ideal.Quotient.lift (idealOf E I (Uof V)) (θ V).hom (hker V)) = θ V := by
        ext a; rfl
      erw [this]
      rw [hθ₁, ← Category.assoc, IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec]
    let 𝒱 : (Spec (CommRingCat.of R)).OpenCover :=
      Scheme.Cover.mkOfCovers ι₀ (fun V => (V.1.1 : Scheme.{u})) (fun V => V.1.1.ι) (by
        intro x
        have hx : x ∈ (⨆ V : ι₀, V.1.1) := by rw [iSup_small_eq_top]; trivial
        obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
        exact ⟨V, ⟨x, hV⟩, rfl⟩)
    refine ⟨𝒱.glueMorphisms zloc ?_, ?_⟩
    · intro V W
      rw [← cancel_mono (J E I hI).subschemeι]
      have h1 : (pullback.fst (𝒱.f V) (𝒱.f W) ≫ zloc V) ≫ (J E I hI).subschemeι =
          (pullback.fst (𝒱.f V) (𝒱.f W) ≫ 𝒱.f V) ≫ s := by
        rw [Category.assoc, Category.assoc]; exact congrArg (pullback.fst (𝒱.f V) (𝒱.f W) ≫ ·) (hzloc V)
      have h2 : (pullback.snd (𝒱.f V) (𝒱.f W) ≫ zloc W) ≫ (J E I hI).subschemeι =
          (pullback.snd (𝒱.f V) (𝒱.f W) ≫ 𝒱.f W) ≫ s := by
        rw [Category.assoc, Category.assoc]; exact congrArg (pullback.snd (𝒱.f V) (𝒱.f W) ≫ ·) (hzloc W)
      rw [h1, h2, pullback.condition]
    · apply Scheme.Cover.hom_ext 𝒱
      intro V
      rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms]
      exact hzloc V

end G0
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot.G0"

theorem solution
    (E : Scheme.{u})
    (I : ∀ (R : Type u) [CommRing R], (Spec (CommRingCat.of R) ⟶ E) → Ideal R)
    (hI : ∀ (R R' : Type u) [CommRing R] [CommRing R'] (ψ : R →+* R') (s : Spec (CommRingCat.of R) ⟶ E),
      I R' (Spec.map (CommRingCat.ofHom ψ) ≫ s) = (I R s).map ψ) :
    ∃ (Z : Scheme.{u}) (ι : Z ⟶ E), IsClosedImmersion ι ∧
      ∀ (R : Type u) [CommRing R] (s : Spec (CommRingCat.of R) ⟶ E),
        (∃ z : Spec (CommRingCat.of R) ⟶ Z, z ≫ ι = s) ↔ I R s = ⊥ :=
  G0.main I hI

end S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_exists_isClosedImmersion_forall_exists_comp_eq_iff_ideal_eq_bot (solution)
