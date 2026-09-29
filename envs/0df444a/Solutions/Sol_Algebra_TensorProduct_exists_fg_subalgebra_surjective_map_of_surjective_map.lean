-- Prove2me | solution 1 for Algebra.TensorProduct.exists_fg_subalgebra_surjective_map_of_surjective_map
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/168c8c52-72e5-5795-9e7c-1f955a3abfcf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map

set_option autoImplicit false

open TensorProduct

universe u

namespace SurjDescGC3

variable {R A D C : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing C] [Algebra R A] [Algebra R D] [Algebra R C]
  (φ : D →ₐ[R] C)

theorem rTensor_comp_map (T : Subalgebra R A) (w : ↥T ⊗[R] D) :
    (LinearMap.rTensor C T.val.toLinearMap) (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ w) =
      Algebra.TensorProduct.map (AlgHom.id A A) φ (LinearMap.rTensor D T.val.toLinearMap w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul t d => simp
  | add x y hx hy => simp [map_add, hx, hy]

theorem rTensor_incl_map {T T' : Subalgebra R A} (h : T ≤ T') (w : ↥T ⊗[R] D) :
    (LinearMap.rTensor C (Subalgebra.inclusion h).toLinearMap) (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ w) =
      Algebra.TensorProduct.map (AlgHom.id ↥T' ↥T') φ (LinearMap.rTensor D (Subalgebra.inclusion h).toLinearMap w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul t d => simp
  | add x y hx hy => simp [map_add, hx, hy]

theorem step (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ))
    (T₀ : Subalgebra R A) (hT₀ : T₀.FG) (c : C) :
    ∃ (T : Subalgebra R A) (_ : T₀ ≤ T), T.FG ∧
      (1 : ↥T) ⊗ₜ[R] c ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
  classical
  obtain ⟨w, hw⟩ := hA ((1 : A) ⊗ₜ[R] c)
  obtain ⟨T₁, hT₁, ⟨w₁, hw₁⟩⟩ := TensorProduct.Algebra.exists_of_fg w

  let T₂ := T₀ ⊔ T₁
  have hT₂ : T₂.FG := hT₀.sup hT₁
  let w₂ : ↥T₂ ⊗[R] D := LinearMap.rTensor D (Subalgebra.inclusion (le_sup_right : T₁ ≤ T₂)).toLinearMap w₁

  have heq : LinearMap.rTensor C T₂.val.toLinearMap (Algebra.TensorProduct.map (AlgHom.id ↥T₂ ↥T₂) φ w₂) =
      LinearMap.rTensor C T₂.val.toLinearMap ((1 : ↥T₂) ⊗ₜ[R] c) := by
    rw [rTensor_comp_map]
    have : LinearMap.rTensor D T₂.val.toLinearMap w₂ = w := by
      rw [← hw₁]; show (LinearMap.rTensor D T₂.val.toLinearMap) ((LinearMap.rTensor D _) w₁) = _
      rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]; rfl
    rw [this, hw]
    simp
  obtain ⟨T, hT₂T, hT, h⟩ := TensorProduct.Algebra.eq_of_fg_of_subtype_eq hT₂ heq
  refine ⟨T, le_sup_left.trans hT₂T, hT, ⟨LinearMap.rTensor D (Subalgebra.inclusion hT₂T).toLinearMap w₂, ?_⟩⟩
  rw [← rTensor_incl_map, h]
  simp

end SurjDescGC3

theorem solution
    {R A D C : Type u} [CommRing R] [CommRing A] [CommRing D] [CommRing C] [Algebra R A] [Algebra R D] [Algebra R C]
    (φ : D →ₐ[R] C) (hφ : φ.toRingHom.FiniteType)
    (hA : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id A A) φ)) (s : Finset A) :
    ∃ (T : Subalgebra R A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
  classical
  letI algDC : Algebra D C := φ.toRingHom.toAlgebra
  have hft : Algebra.FiniteType D C := hφ
  obtain ⟨gens, hgens⟩ := hft.out

  have key : ∀ (l : List C), ∃ (T : Subalgebra R A), Algebra.adjoin R (↑s : Set A) ≤ T ∧ T.FG ∧
      ∀ c ∈ l, (1 : ↥T) ⊗ₜ[R] c ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ) := by
    intro l
    induction l with
    | nil => exact ⟨Algebra.adjoin R (↑s : Set A), le_rfl, Subalgebra.fg_adjoin_finset _, fun c hc => by simp at hc⟩
    | cons c l ih =>
      obtain ⟨T₀, hsT₀, hT₀, hl⟩ := ih
      obtain ⟨T, hT₀T, hT, hc⟩ := SurjDescGC3.step φ hA T₀ hT₀ c
      refine ⟨T, hsT₀.trans hT₀T, hT, fun c' hc' => ?_⟩
      rcases List.mem_cons.mp hc' with rfl | hmem
      · exact hc
      · obtain ⟨w, hw⟩ := hl c' hmem
        refine ⟨LinearMap.rTensor D (Subalgebra.inclusion hT₀T).toLinearMap w, ?_⟩
        rw [← SurjDescGC3.rTensor_incl_map, hw]; simp
  obtain ⟨T, hsT, hT, hgen⟩ := key gens.toList
  refine ⟨T, hT, fun a ha => hsT (Algebra.subset_adjoin ha), ?_⟩

  let ψ := Algebra.TensorProduct.map (AlgHom.id ↥T ↥T) φ
  have h1c : ∀ c : C, (1 : ↥T) ⊗ₜ[R] c ∈ Set.range ψ := by
    intro c
    have hc : c ∈ Algebra.adjoin D (↑gens : Set C) := by rw [hgens]; trivial
    induction hc using Algebra.adjoin_induction with
    | mem x hx => exact hgen x (Finset.mem_toList.mpr hx)
    | algebraMap d => exact ⟨(1 : ↥T) ⊗ₜ[R] d, by simp [ψ]; rfl⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb, TensorProduct.tmul_add]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a * b, by rw [map_mul, ha, hb, Algebra.TensorProduct.tmul_mul_tmul, one_mul]⟩
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul t c =>
    obtain ⟨a, ha⟩ := h1c c
    refine ⟨(t ⊗ₜ[R] (1 : D)) * a, ?_⟩
    rw [map_mul, ha]
    simp [ψ, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, ha, hb]⟩

end S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map
end P2MW
export P2MW.S_Algebra_TensorProduct_exists_fg_subalgebra_surjective_map_of_surjective_map (solution)
