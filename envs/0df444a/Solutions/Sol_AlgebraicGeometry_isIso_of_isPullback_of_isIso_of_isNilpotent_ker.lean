-- Prove2me | solution 1 for AlgebraicGeometry.isIso_of_isPullback_of_isIso_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e2ebf874-82c8-5b5b-85ad-236f430a0953

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace K6IsoLiftAux

section Algebra

open TensorProduct

variable {T : Type*} [CommRing T]

theorem submodule_eq_bot_of_le_smul_of_isNilpotent {M : Type*} [AddCommGroup M] [Module T M]
    (N : Ideal T) (hN : IsNilpotent N) (P : Submodule T M) (h : P ≤ N • P) : P = ⊥ := by
  obtain ⟨k, hk⟩ := hN
  have key : ∀ n : ℕ, P ≤ N ^ n • P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc P ≤ N • P := h
        _ ≤ N • (N ^ n • P) := Submodule.smul_mono le_rfl ih
        _ = (N * N ^ n) • P := (Submodule.mul_smul _ _ _).symm
        _ = N ^ (n + 1) • P := by rw [pow_succ']
  have := key k
  rw [hk, Ideal.zero_eq_bot, Submodule.bot_smul] at this
  exact le_bot_iff.mp this

theorem submodule_eq_top_of_le_sup_smul_of_isNilpotent {M : Type*} [AddCommGroup M] [Module T M]
    (N : Ideal T) (hN : IsNilpotent N) (P : Submodule T M) (h : (⊤ : Submodule T M) ≤ P ⊔ N • ⊤) :
    P = ⊤ := by
  obtain ⟨k, hk⟩ := hN
  have key : ∀ n : ℕ, (⊤ : Submodule T M) ≤ P ⊔ N ^ n • ⊤ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc (⊤ : Submodule T M) ≤ P ⊔ N • ⊤ := h
        _ ≤ P ⊔ N • (P ⊔ N ^ n • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl ih) _
        _ = P ⊔ (N • P ⊔ (N * N ^ n) • ⊤) := by rw [Submodule.smul_sup, Submodule.mul_smul]
        _ ≤ P ⊔ N ^ (n + 1) • ⊤ := by
          rw [pow_succ']
          exact sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)
  have := key k
  rw [hk, Ideal.zero_eq_bot, Submodule.bot_smul, sup_bot_eq] at this
  exact top_le_iff.mp this

noncomputable def smulMap (N : Ideal T) (M : Type*) [AddCommGroup M] [Module T M] :
    N ⊗[T] M →ₗ[T] M :=
  (TensorProduct.lid T M).toLinearMap ∘ₗ (N.subtype.rTensor M)

theorem smulMap_tmul (N : Ideal T) {M : Type*} [AddCommGroup M] [Module T M] (n : N) (m : M) :
    smulMap N M (n ⊗ₜ m) = (n : T) • m := by
  simp [smulMap]

theorem smulMap_injective_of_flat (N : Ideal T) (M : Type*) [AddCommGroup M] [Module T M]
    [Module.Flat T M] : Function.Injective (smulMap N M) := by
  unfold smulMap
  exact (TensorProduct.lid T M).injective.comp
    (Module.Flat.rTensor_preserves_injective_linearMap _ N.injective_subtype)

theorem smul_top_le_range_smulMap (N : Ideal T) (M : Type*) [AddCommGroup M] [Module T M] :
    (N • ⊤ : Submodule T M) ≤ LinearMap.range (smulMap N M) := by
  refine Submodule.smul_le.mpr fun n hn m _ => ?_
  exact ⟨⟨n, hn⟩ ⊗ₜ m, smulMap_tmul N ⟨n, hn⟩ m⟩

theorem ker_inf_smul_top_le_smul_ker {A B : Type*} [AddCommGroup A] [Module T A] [AddCommGroup B]
    [Module T B] [Module.Flat T A] (u : B →ₗ[T] A) (hu : Function.Surjective u) (N : Ideal T) :
    LinearMap.ker u ⊓ (N • ⊤ : Submodule T B) ≤ N • LinearMap.ker u := by
  intro b hb
  obtain ⟨hbK, hbN⟩ := hb
  obtain ⟨β, hβ⟩ := smul_top_le_range_smulMap N B hbN

  have hnat : ∀ γ : N ⊗[T] B, smulMap N A (LinearMap.lTensor N u γ) = u (smulMap N B γ) := by
    intro γ
    induction γ using TensorProduct.induction_on with
    | zero => simp
    | tmul n b' => simp [smulMap_tmul]
    | add x y hx hy => simp [map_add, hx, hy]
  have hβ0 : LinearMap.lTensor N u β = 0 := by
    apply smulMap_injective_of_flat N A
    rw [hnat, hβ, map_zero]
    exact hbK
  have hex : Function.Exact (LinearMap.lTensor N (LinearMap.ker u).subtype) (LinearMap.lTensor N u) :=
    lTensor_exact N (by rw [LinearMap.exact_iff]; exact (Submodule.range_subtype _).symm) hu
  obtain ⟨γ, hγ⟩ := (hex β).mp hβ0
  have hrange : ∀ δ : N ⊗[T] LinearMap.ker u,
      smulMap N B (LinearMap.lTensor N (LinearMap.ker u).subtype δ) ∈ N • LinearMap.ker u := by
    intro δ
    induction δ using TensorProduct.induction_on with
    | zero => simp
    | tmul n k =>
      simp only [LinearMap.lTensor_tmul, smulMap_tmul, Submodule.coe_subtype]
      exact Submodule.smul_mem_smul n.2 k.2
    | add x y hx hy =>
      simp only [map_add]
      exact Submodule.add_mem _ hx hy
  rw [← hβ, ← hγ]
  exact hrange γ

variable {A B A₀ B₀ : Type*} [CommRing A] [CommRing B] [CommRing A₀] [CommRing B₀]

theorem bijective_of_bijective_reduction
    (iA : T →+* A) (iB : T →+* B) (u : B →+* A) (hu : u.comp iB = iA)
    (sA : A →+* A₀) (sB : B →+* B₀) (hsB : Function.Surjective sB) (u₀ : B₀ →+* A₀)
    (hsq : sA.comp u = u₀.comp sB)
    (N : Ideal T) (hN : IsNilpotent N)
    (hkA : RingHom.ker sA ≤ N.map iA) (hkB : RingHom.ker sB ≤ N.map iB)
    (hA : iA.Flat) (hu₀ : Function.Bijective u₀) :
    Function.Bijective u := by
  letI algA : Algebra T A := iA.toAlgebra
  letI algB : Algebra T B := iB.toAlgebra
  haveI : Module.Flat T A := hA

  let uₗ : B →ₗ[T] A :=
    { toFun := u
      map_add' := fun x y => map_add u x y
      map_smul' := fun t b => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact congrArg (fun h : T →+* A => h t) hu }
  have huₗ : ∀ b, uₗ b = u b := fun _ => rfl
  have hsq' : ∀ b, sA (u b) = u₀ (sB b) := fun b => congrArg (fun h : B →+* A₀ => h b) hsq
  have hNA : (N.map iA : Ideal A).restrictScalars T = N • (⊤ : Submodule T A) := by
    rw [Ideal.smul_top_eq_map]; rfl
  have hNB : (N.map iB : Ideal B).restrictScalars T = N • (⊤ : Submodule T B) := by
    rw [Ideal.smul_top_eq_map]; rfl

  have hsurj : Function.Surjective u := by
    have hrange : LinearMap.range uₗ = ⊤ := by
      apply submodule_eq_top_of_le_sup_smul_of_isNilpotent N hN
      intro a _
      obtain ⟨b₀, hb₀⟩ := hu₀.2 (sA a)
      obtain ⟨b, rfl⟩ := hsB b₀
      have hmem : a - u b ∈ RingHom.ker sA := by
        rw [RingHom.mem_ker, map_sub, hsq' b, hb₀, sub_self]
      have hmem' : a - u b ∈ N • (⊤ : Submodule T A) := by
        rw [← hNA]; exact hkA hmem
      have : a = uₗ b + (a - u b) := by simp [huₗ]
      rw [this]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hmem'
    intro a
    have : a ∈ LinearMap.range uₗ := hrange ▸ Submodule.mem_top
    obtain ⟨b, hb⟩ := this
    exact ⟨b, hb⟩

  have hinj : Function.Injective u := by
    have hker : LinearMap.ker uₗ = ⊥ := by
      apply submodule_eq_bot_of_le_smul_of_isNilpotent N hN
      intro b hb
      refine ker_inf_smul_top_le_smul_ker uₗ hsurj N ⟨hb, ?_⟩
      have hb' : u b = 0 := hb
      have : sB b = 0 := by
        apply hu₀.1
        rw [← hsq' b, hb', map_zero, map_zero]
      rw [← hNB]
      exact hkB this
    intro b₁ b₂ h
    have : b₁ - b₂ ∈ LinearMap.ker uₗ := by
      rw [LinearMap.mem_ker, map_sub]; simp [huₗ, h]
    rw [hker] at this
    exact sub_eq_zero.mp this
  exact ⟨hinj, hsurj⟩

end Algebra

end K6IsoLiftAux

open K6IsoLiftAux in
theorem solution
    (T' T : Type u) [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {X Y X₀ Y₀ : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of T')) (q : Y ⟶ Spec (CommRingCat.of T'))
    [Flat p] [LocallyOfFinitePresentation p] [Flat q] [LocallyOfFinitePresentation q]
    (φ : X ⟶ Y) (hφ : φ ≫ q = p)
    (p₀ : X₀ ⟶ Spec (CommRingCat.of T)) (q₀ : Y₀ ⟶ Spec (CommRingCat.of T))
    (gX : X₀ ⟶ X) (hX : IsPullback gX p₀ p (Spec.map (CommRingCat.ofHom π)))
    (gY : Y₀ ⟶ Y) (hY : IsPullback gY q₀ q (Spec.map (CommRingCat.ofHom π)))
    (φ₀ : X₀ ⟶ Y₀) (hφ₀ : φ₀ ≫ gY = gX ≫ φ) (hφ₀q : φ₀ ≫ q₀ = p₀) [IsIso φ₀] :
    IsIso φ := by
  obtain ⟨_, hXsurj, hXhomeo⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker π hπ hker p p₀ gX hX
  obtain ⟨_, hYsurj, hYhomeo⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker π hπ hker q q₀ gY hY
  have hcomm : gX ≫ φ = φ₀ ≫ gY := hφ₀.symm
  rw [isIso_iff_isIso_stalkMap]
  refine ⟨?_, ?_⟩
  ·
    rw [TopCat.isIso_iff_isHomeomorph]
    have hφ₀h : IsHomeomorph φ₀.base := (TopCat.isIso_iff_isHomeomorph _).mp inferInstance
    have h1 : IsHomeomorph (φ.base ∘ gX.base) := by
      have : (φ.base : X → Y) ∘ gX.base = gY.base ∘ φ₀.base := by
        funext x
        change (gX ≫ φ) x = (φ₀ ≫ gY) x
        rw [hcomm]
      rw [this]
      exact hYhomeo.comp hφ₀h
    have h2 : (φ.base : X → Y) = (φ.base ∘ gX.base) ∘ hXhomeo.homeomorph.symm := by
      funext x
      simp only [Function.comp_apply]
      congr 1
      exact (hXhomeo.homeomorph.apply_symm_apply x).symm
    rw [h2]
    exact h1.comp hXhomeo.homeomorph.symm.isHomeomorph
  · intro x
    obtain ⟨x₀, rfl⟩ := gX.surjective x

    obtain ⟨_, hkX⟩ :=
      AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
        π hπ p gX p₀ hX x₀
    obtain ⟨hsYsurj, hkY⟩ :=
      AlgebraicGeometry.stalkMap_surjective_and_ker_stalkMap_eq_map_ker_of_isPullback_of_surjective
        π hπ q gY q₀ hY (φ₀ x₀)
    have hpt : φ (gX x₀) = gY (φ₀ x₀) := by
      change (gX ≫ φ) x₀ = (φ₀ ≫ gY) x₀
      rw [hcomm]

    have key := Scheme.Hom.stalkMap_congr_hom (gX ≫ φ) (φ₀ ≫ gY) hcomm x₀
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at key
    obtain ⟨ι, hι, hιgerm⟩ : ∃ ι : Y.presheaf.stalk (φ (gX x₀)) ≅ Y.presheaf.stalk (gY (φ₀ x₀)),
        φ.stalkMap (gX x₀) ≫ gX.stalkMap x₀ = ι.hom ≫ gY.stalkMap (φ₀ x₀) ≫ φ₀.stalkMap x₀ ∧
        ∀ s, ι.hom (Y.presheaf.germ ⊤ (φ (gX x₀)) trivial s) =
          Y.presheaf.germ ⊤ (gY (φ₀ x₀)) trivial s :=
      ⟨_, key, fun s => by
        change (Y.presheaf.germ ⊤ _ trivial ≫ Y.presheaf.stalkSpecializes
          (specializes_of_eq hpt.symm : (φ₀ ≫ gY) x₀ ⤳ (gX ≫ φ) x₀)) s = _
        rw [TopCat.Presheaf.germ_stalkSpecializes]
        rfl⟩
    have hιbij : Function.Bijective ι.hom := ConcreteCategory.bijective_of_isIso ι.hom

    let e := (Scheme.ΓSpecIso (CommRingCat.of T')).inv
    let iA : T' →+* X.presheaf.stalk (gX x₀) :=
      (X.presheaf.germ ⊤ (gX x₀) trivial).hom.comp (p.appTop.hom.comp e.hom)
    let iB : T' →+* Y.presheaf.stalk (φ (gX x₀)) :=
      (Y.presheaf.germ ⊤ (φ (gX x₀)) trivial).hom.comp (q.appTop.hom.comp e.hom)

    have hA : iA.Flat := by
      let j : T' →+* (Spec (CommRingCat.of T')).presheaf.stalk (p (gX x₀)) :=
        ((Spec (CommRingCat.of T')).presheaf.germ ⊤ (p (gX x₀)) trivial).hom.comp e.hom
      have hj : iA = (p.stalkMap (gX x₀)).hom.comp j := by
        ext t
        simp only [iA, j, RingHom.comp_apply]
        rw [Scheme.Hom.germ_stalkMap_apply]
        rfl
      have hjflat : j.Flat := by
        have : j = algebraMap T' ((Spec.structureSheaf T').presheaf.stalk (p (gX x₀))) := rfl
        rw [this]
        exact (RingHom.flat_algebraMap_iff
          (S := (Spec.structureSheaf T').presheaf.stalk (p (gX x₀)))).mpr
          (IsLocalization.flat ((Spec.structureSheaf T').presheaf.stalk (p (gX x₀)))
            (p (gX x₀)).asIdeal.primeCompl)
      rw [hj]
      exact RingHom.Flat.comp hjflat (Flat.stalkMap p (gX x₀))
    have hbij : Function.Bijective (φ.stalkMap (gX x₀)).hom := by
      refine bijective_of_bijective_reduction (T := T') iA iB (φ.stalkMap (gX x₀)).hom ?_
        (gX.stalkMap x₀).hom ((gY.stalkMap (φ₀ x₀)).hom.comp ι.hom.hom) ?_ (φ₀.stalkMap x₀).hom ?_
        (RingHom.ker π) hker hkX.le ?_ hA ?_
      ·
        ext t
        simp only [iA, iB, RingHom.comp_apply]
        rw [Scheme.Hom.germ_stalkMap_apply]
        subst hφ
        rfl
      · exact hsYsurj.comp hιbij.2
      · ext b
        change (φ.stalkMap (gX x₀) ≫ gX.stalkMap x₀) b = (ι.hom ≫ gY.stalkMap (φ₀ x₀) ≫ φ₀.stalkMap x₀) b
        rw [hι]
      ·
        intro b hb
        have hb' : ι.hom b ∈ RingHom.ker (gY.stalkMap (φ₀ x₀)).hom := hb
        rw [hkY] at hb'
        have hiB : ((Y.presheaf.germ ⊤ (gY (φ₀ x₀)) trivial).hom.comp (q.appTop.hom.comp e.hom)) =
            ι.hom.hom.comp iB := by
          ext t
          simp only [iB, RingHom.comp_apply]
          exact (hιgerm _).symm
        rw [hiB, ← Ideal.map_map] at hb'
        have := Ideal.mem_comap.mpr hb'
        rwa [Ideal.comap_map_of_bijective _ hιbij] at this
      · exact ConcreteCategory.bijective_of_isIso (φ₀.stalkMap x₀)
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij

end S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker
end P2MW
export P2MW.S_AlgebraicGeometry_isIso_of_isPullback_of_isIso_of_isNilpotent_ker (solution)
