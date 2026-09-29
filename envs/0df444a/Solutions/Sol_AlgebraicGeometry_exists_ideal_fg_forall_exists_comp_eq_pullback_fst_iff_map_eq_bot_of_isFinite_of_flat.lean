-- Prove2me | solution 1 for AlgebraicGeometry.exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/9065f8db-5f58-5ed1-8652-e0c32e27be15

import Mathlib
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

universe u

namespace EngineW

theorem exists_fg_ideal_forall_tmul_eq_zero_iff_map_eq_bot
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Projective R M]
    (N : Submodule R M) (hN : N.FG) :
    ∃ I : Ideal R, I.FG ∧ ∀ (T : Type u) [CommRing T] [Algebra R T],
      (∀ n ∈ N, n ⊗ₜ[R] (1 : T) = (0 : M ⊗[R] T)) ↔ Ideal.map (algebraMap R T) I = ⊥ := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  obtain ⟨G, rfl⟩ := hN
  refine ⟨Ideal.span ↑(G.biUnion fun g => (s g).support.image (s g)), ⟨_, rfl⟩, ?_⟩
  intro T _ _
  have coord : ∀ (g : M) (i : M),
      finsuppScalarRight R T T M ((1 : T) ⊗ₜ[R] (s g)) i = algebraMap R T (s g i) := by
    intro g i
    rw [finsuppScalarRight_apply_tmul_apply, Algebra.algebraMap_eq_smul_one]
  have hsg : ∀ g : M, Finsupp.linearCombination R (id : M → M) (s g) = g := fun g =>
    LinearMap.congr_fun hs g

  have swap : ∀ n : M, n ⊗ₜ[R] (1 : T) = (0 : M ⊗[R] T) ↔ (1 : T) ⊗ₜ[R] n = (0 : T ⊗[R] M) := by
    intro n
    constructor
    · intro h; rw [← TensorProduct.comm_tmul R M T n 1, h, map_zero]
    · intro h; rw [← TensorProduct.comm_tmul R T M 1 n, h, map_zero]
  simp_rw [swap]
  constructor
  · intro h
    rw [Ideal.map_span, Ideal.span_eq_bot]
    rintro x ⟨c, hc, rfl⟩
    simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, Finset.mem_image, exists_prop] at hc
    obtain ⟨g, hgG, i, -, rfl⟩ := hc
    have h1 : (1 : T) ⊗ₜ[R] (s g) = 0 := by
      rw [← LinearMap.lTensor_tmul T s (1 : T) g, h g (Submodule.subset_span hgG), map_zero]
    rw [← coord g i, h1, map_zero, Finsupp.zero_apply]
  · intro h n hn
    rw [Ideal.map_span, Ideal.span_eq_bot] at h
    refine Submodule.span_induction (p := fun n _ => (1 : T) ⊗ₜ[R] n = (0 : T ⊗[R] M)) ?_ ?_ ?_ ?_ hn
    · intro g hgG
      have h1 : (1 : T) ⊗ₜ[R] (s g) = 0 := by
        rw [← (finsuppScalarRight R T T M).map_eq_zero_iff]
        ext i
        rw [coord, Finsupp.zero_apply]
        by_cases hi : i ∈ (s g).support
        · exact h _ ⟨s g i, by
            simp only [Finset.coe_biUnion, Finset.mem_coe, Set.mem_iUnion, Finset.mem_image, exists_prop]
            exact ⟨g, hgG, i, hi, rfl⟩, rfl⟩
        · rw [Finsupp.notMem_support_iff.mp hi, map_zero]
      rw [← hsg g, ← LinearMap.lTensor_tmul T (Finsupp.linearCombination R (id : M → M)) (1 : T) (s g), h1,
        map_zero]
    · exact tmul_zero _ _
    · intro x y _ _ hx hy
      rw [tmul_add, hx, hy, add_zero]
    · intro r x _ hx
      rw [tmul_smul, hx, smul_zero]

theorem exists_comp_eq_fst_iff {X X' Y Z V : Scheme.{u}} (f : X ⟶ Z) (f' : X' ⟶ Z) (g g' : Y ⟶ Z)
    (e : X ≅ X') (he : f = e.hom ≫ f') (hg : g = g') (w : V ⟶ X) :
    (∃ ℓ : pullback f g ⟶ V, ℓ ≫ w = pullback.fst f g) ↔
      (∃ ℓ' : pullback f' g' ⟶ V, ℓ' ≫ (w ≫ e.hom) = pullback.fst f' g') := by
  subst hg
  have he' : e.inv ≫ f = f' := by rw [he, Iso.inv_hom_id_assoc]
  constructor
  · rintro ⟨ℓ, hℓ⟩
    refine ⟨pullback.lift (pullback.fst f' g ≫ e.inv) (pullback.snd f' g)
        (by rw [Category.assoc, he']; exact pullback.condition) ≫ ℓ, ?_⟩
    rw [Category.assoc, ← Category.assoc ℓ, hℓ, ← Category.assoc, pullback.lift_fst, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  · rintro ⟨ℓ', hℓ'⟩
    refine ⟨pullback.lift (pullback.fst f g ≫ e.hom) (pullback.snd f g)
        (by rw [Category.assoc, ← he]; exact pullback.condition) ≫ ℓ', ?_⟩
    have hℓ'' : ℓ' ≫ w = pullback.fst f' g ≫ e.inv := by
      rw [← hℓ', Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Category.assoc, hℓ'', ← Category.assoc, pullback.lift_fst, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]

theorem exists_comp_eq_iff_of_iso {P Q V X : Scheme.{u}} (i : P ≅ Q) (p : P ⟶ X) (q : Q ⟶ X) (hi : i.inv ≫ p = q)
    (v : V ⟶ X) :
    (∃ ℓ : P ⟶ V, ℓ ≫ v = p) ↔ (∃ y : Q ⟶ V, y ≫ v = q) := by
  constructor
  · rintro ⟨ℓ, hℓ⟩; exact ⟨i.inv ≫ ℓ, by rw [Category.assoc, hℓ, hi]⟩
  · rintro ⟨y, hy⟩; refine ⟨i.hom ≫ y, ?_⟩; rw [Category.assoc, hy, ← hi, Iso.hom_inv_id_assoc]

end EngineW

theorem solution
    (S : Type u) [CommRing S] (C W : Scheme.{u}) (c : C ⟶ Spec (CommRingCat.of S))
    [IsFinite c] [Flat c] [LocallyOfFinitePresentation c]
    (w : W ⟶ C) [IsClosedImmersion w] [LocallyOfFinitePresentation w] :
    ∃ J : Ideal S, J.FG ∧ ∀ (T : Type u) [CommRing T] (ψ : S →+* T),
      (∃ ℓ : pullback c (Spec.map (CommRingCat.ofHom ψ)) ⟶ W,
          ℓ ≫ w = pullback.fst c (Spec.map (CommRingCat.ofHom ψ))) ↔ J.map ψ = ⊥ := by
  classical
  haveI : IsAffine C := isAffine_of_isAffineHom c
  let B : Type u := Γ(C, ⊤)
  let e : C ≅ Spec (CommRingCat.of B) := C.isoSpec
  obtain ⟨φ₀, hφ₀⟩ := Spec.map_surjective (e.inv ≫ c)
  letI : Algebra S B := φ₀.hom.toAlgebra
  have hc : c = e.hom ≫ Spec.map φ₀ := by rw [hφ₀, Iso.hom_inv_id_assoc]

  have hfin : IsFinite (Spec.map φ₀) := by rw [hφ₀]; infer_instance
  have hflat : Flat (Spec.map φ₀) := by rw [hφ₀]; infer_instance
  have hlfp : LocallyOfFinitePresentation (Spec.map φ₀) := by rw [hφ₀]; infer_instance
  haveI hB₁ : Module.Finite S B := (IsFinite.SpecMap_iff φ₀).mp hfin
  haveI hB₂ : Module.Flat S B := Flat.SpecMap_iff.mp hflat
  have hB₃ : Algebra.FinitePresentation S B := (LocallyOfFinitePresentation.SpecMap_iff φ₀).mp hlfp
  haveI : Module.FinitePresentation S B :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite S B).mpr hB₃
  haveI : Module.Projective S B := Module.Flat.projective_of_finitePresentation

  obtain ⟨J₀, hJ₀fg, hJ₀⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_ideal_fg_forall_exists_comp_eq_specMap_iff_map_eq_bot (w ≫ e.hom)

  obtain ⟨J, hJfg, hJ⟩ := EngineW.exists_fg_ideal_forall_tmul_eq_zero_iff_map_eq_bot (J₀.restrictScalars S)
    (Submodule.FG.restrictScalars (R := S) (show Submodule.FG (J₀ : Submodule B B) from hJ₀fg))
  refine ⟨J, hJfg, fun T _ ψ => ?_⟩
  letI : Algebra S T := ψ.toAlgebra

  rw [EngineW.exists_comp_eq_fst_iff c (Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (Spec.map (CommRingCat.ofHom ψ)) (Spec.map (CommRingCat.ofHom (algebraMap S T))) e hc rfl w]

  rw [EngineW.exists_comp_eq_iff_of_iso (pullbackSpecIso S B T) _ _ (pullbackSpecIso_inv_fst S B T) (w ≫ e.hom)]

  rw [hJ₀ (B ⊗[S] T) Algebra.TensorProduct.includeLeftRingHom, Ideal.map_eq_bot_iff_le_ker]

  change _ ↔ Ideal.map (algebraMap S T) J = ⊥
  rw [← hJ T]
  exact ⟨fun h n hn => h hn, fun h j hj => h j hj⟩

end S_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_ideal_fg_forall_exists_comp_eq_pullback_fst_iff_map_eq_bot_of_isFinite_of_flat (solution)
