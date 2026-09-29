-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/c7b61227-da7f-58ce-a573-ccc91043b66f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

theorem IsoCrit.bijective_algebraMap_of_finite_of_retraction_of_forall_algHom_eq_of_isAlgClosed
    {R : Type u} [CommRing R] (C : Type u) [CommRing C] [Algebra R C] [Module.Finite R C]
    (σ : C →ₐ[R] R)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R k] (T : Type u) [CommRing T] [Algebra R T]
      [Algebra k T] [IsScalarTower R k T] (g₁ g₂ : C →ₐ[R] T), g₁ = g₂) :
    Function.Bijective (algebraMap R C) := by
  classical
  refine ⟨fun a b hab => by simpa using congrArg σ hab, ?_⟩
  set N : Submodule R C := LinearMap.range (Algebra.linearMap R C) with hN

  suffices hQ : Subsingleton (C ⧸ N) by
    have hNtop : N = ⊤ := Submodule.Quotient.subsingleton_iff.mp hQ
    intro c
    have hc : c ∈ N := hNtop ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := hc
    exact ⟨r, hr⟩

  have key : ∀ (𝔪 : Ideal R), 𝔪.IsMaximal → (⊤ : Submodule R (C ⧸ N)) ≤ 𝔪 • ⊤ := by
    intro 𝔪 h𝔪
    letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    let kb : Type u := AlgebraicClosure (R ⧸ 𝔪)
    have hg := h kb (kb ⊗[R] C) Algebra.TensorProduct.includeRight ((Algebra.ofId R (kb ⊗[R] C)).comp σ)
    have h0 : (N.mkQ (1 : C)) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨1, by simp⟩
    have h1 : ∀ c : C, (1 : kb) ⊗ₜ[R] (N.mkQ c) = 0 := by
      intro c
      have hc := congrArg (fun g : C →ₐ[R] kb ⊗[R] C => LinearMap.lTensor kb N.mkQ (g c)) hg
      simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.comp_apply, Algebra.ofId_apply,
        LinearMap.lTensor_tmul] at hc
      rw [Algebra.algebraMap_eq_smul_one, map_smul, Algebra.TensorProduct.one_def, LinearMap.lTensor_tmul, h0,
        tmul_zero, smul_zero] at hc
      exact hc
    have h2 : ∀ q : C ⧸ N, (1 : kb) ⊗ₜ[R] q = 0 := fun q => by
      obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective N q
      exact h1 c

    obtain ⟨g, hg1⟩ : ∃ g : kb →ₗ[R ⧸ 𝔪] (R ⧸ 𝔪), g 1 = 1 := by
      obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap (R ⧸ 𝔪) kb)
        (LinearMap.ker_eq_bot.mpr (algebraMap (R ⧸ 𝔪) kb).injective)
      refine ⟨g, ?_⟩
      have := LinearMap.congr_fun hg 1
      simpa using this
    have h3 : ∀ q : C ⧸ N, (1 : R ⧸ 𝔪) ⊗ₜ[R] q = 0 := fun q => by
      let F : kb ⊗[R] (C ⧸ N) →ₗ[R] (R ⧸ 𝔪) ⊗[R] (C ⧸ N) :=
        _root_.TensorProduct.map (g.restrictScalars R) LinearMap.id
      have hq := congrArg F (h2 q)
      have hF : F ((1 : kb) ⊗ₜ[R] q) = g 1 ⊗ₜ[R] q := _root_.TensorProduct.map_tmul _ _ _ _
      rw [map_zero, hF, hg1] at hq
      exact hq
    have h4 : Subsingleton ((R ⧸ 𝔪) ⊗[R] (C ⧸ N)) := by
      refine ⟨fun x y => ?_⟩
      suffices hz : ∀ z : (R ⧸ 𝔪) ⊗[R] (C ⧸ N), z = 0 by rw [hz x, hz y]
      intro z
      induction z using _root_.TensorProduct.induction_on with
      | zero => rfl
      | tmul a q =>
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
          have hr : (Ideal.Quotient.mk 𝔪 r : R ⧸ 𝔪) = r • (1 : R ⧸ 𝔪) := by
            rw [Algebra.smul_def, mul_one]; rfl
          rw [hr, ← _root_.TensorProduct.smul_tmul', h3, smul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    haveI := h4
    have h5 : Subsingleton ((C ⧸ N) ⧸ (𝔪 • (⊤ : Submodule R (C ⧸ N)))) :=
      (_root_.TensorProduct.quotTensorEquivQuotSMul (C ⧸ N) 𝔪).symm.toEquiv.subsingleton
    exact (Submodule.Quotient.subsingleton_iff.mp h5).ge

  by_contra hne
  have hJ : Module.annihilator R (C ⧸ N) ≠ ⊤ := by
    intro hJ
    apply hne
    have h1 : (1 : R) ∈ Module.annihilator R (C ⧸ N) := hJ ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    exact ⟨fun x y => by rw [← one_smul R x, ← one_smul R y, h1, h1]⟩
  obtain ⟨𝔪, h𝔪, hJ𝔪⟩ := Ideal.exists_le_maximal _ hJ
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪
    (⊤ : Submodule R (C ⧸ N)) Module.Finite.fg_top (key 𝔪 h𝔪)
  have hrJ : r ∈ Module.annihilator R (C ⧸ N) := Module.mem_annihilator.mpr fun q => hr q Submodule.mem_top
  have h1𝔪 : (1 : R) ∈ 𝔪 := by
    have := 𝔪.sub_mem (hJ𝔪 hrJ) hr1
    rwa [sub_sub_cancel] at this
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h1𝔪)

open IsoCrit in
theorem solution
    {R : Type u} [CommRing R] {K : Scheme.{u}} (p : K ⟶ Spec (CommRingCat.of R)) [IsFinite p]
    (σ : Spec (CommRingCat.of R) ⟶ K) (hσ : σ ≫ p = 𝟙 _)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (T : Type u) [CommRing T]
      (t' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k))
      (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (a b : Spec (CommRingCat.of T) ⟶ K), a ≫ p = t' ≫ φ → b ≫ p = t' ≫ φ → a = b) :
    IsIso p := by
  classical

  obtain ⟨hKaff, hfin⟩ := HasAffineProperty.iff_of_isAffine.mp ‹IsFinite p›
  haveI : IsAffine K := hKaff
  let R₀ : Type u := Γ(Spec (CommRingCat.of R), ⊤)
  let C : Type u := Γ(K, ⊤)
  letI : Algebra R₀ C := p.appTop.hom.toAlgebra
  haveI : Module.Finite R₀ C := hfin

  let σ₀ : C →ₐ[R₀] R₀ :=
    { toRingHom := σ.appTop.hom
      commutes' := fun r => by
        change (p.appTop ≫ σ.appTop).hom r = r
        rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
        rfl }

  have huniq : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra R₀ k] (T : Type u) [CommRing T] [Algebra R₀ T]
      [Algebra k T] [IsScalarTower R₀ k T] (g₁ g₂ : C →ₐ[R₀] T), g₁ = g₂ := by
    intro k _ _ _ T _ _ _ _ g₁ g₂
    let t' : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (algebraMap k T))
    let φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R₀ k)) ≫ (Spec (CommRingCat.of R)).isoSpec.inv
    let pt : (C →ₐ[R₀] T) → (Spec (CommRingCat.of T) ⟶ K) := fun g =>
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ K.isoSpec.inv
    have hpt : ∀ g : C →ₐ[R₀] T, pt g ≫ p = t' ≫ φ := by
      intro g
      simp only [pt, t', φ, Category.assoc]
      rw [← Scheme.isoSpec_inv_naturality p, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
      congr 2
      apply CommRingCat.hom_ext
      ext r
      change g (algebraMap R₀ C r) = algebraMap k T (algebraMap R₀ k r)
      rw [g.commutes, IsScalarTower.algebraMap_apply R₀ k T]
    have hab := h k T t' φ (pt g₁) (pt g₂) (hpt g₁) (hpt g₂)
    have hab' : Spec.map (CommRingCat.ofHom g₁.toRingHom) = Spec.map (CommRingCat.ofHom g₂.toRingHom) := by
      simpa only [pt, cancel_mono] using hab
    have hab'' := Spec.map_injective hab'
    apply AlgHom.ext
    intro c
    exact congrArg (fun (q : CommRingCat.of C ⟶ CommRingCat.of T) => q.hom c) hab''

  have hbij : Function.Bijective (algebraMap R₀ C) :=
    bijective_algebraMap_of_finite_of_retraction_of_forall_algHom_eq_of_isAlgClosed C σ₀ huniq

  haveI : IsIso ((forget CommRingCat).map p.appTop) := (isIso_iff_bijective _).mpr hbij
  haveI : IsIso p.appTop := isIso_of_reflects_iso p.appTop (forget CommRingCat)
  have hp : p = K.isoSpec.hom ≫ Spec.map p.appTop ≫ (Spec (CommRingCat.of R)).isoSpec.inv := by
    rw [Scheme.isoSpec_inv_naturality p, Iso.hom_inv_id_assoc]
  rw [hp]
  infer_instance

end S_AlgebraicGeometry_isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isFinite_of_section_of_forall_isAlgClosed_hom_eq (solution)
