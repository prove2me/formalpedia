-- Prove2me | solution 1 for Algebra.adjoin_div_tensorProduct_bijective_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3af4d5ac-3cb6-53e1-bc78-d86fdb9ae0d9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_adjoin_div_tensorProduct_bijective_of_flat

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {C : Type*} [CommRing C] (I : Ideal C) (a : C)
    (S : Type*) [CommRing S] [Algebra C S] [IsLocalization.Away a S]
    {C' : Type*} [CommRing C'] [Algebra C C'] [Module.Flat C C']
    (S' : Type*) [CommRing S'] [Algebra C' S'] [Algebra C S'] [IsScalarTower C C' S']
    [IsLocalization.Away (algebraMap C C' a) S'] (φ : S →ₐ[C] S') :
    let B : Subalgebra C S := Algebra.adjoin C {x : S | ∃ i ∈ I, x * algebraMap C S a = algebraMap C S i}
    let B' : Subalgebra C' S' :=
      Algebra.adjoin C' {x : S' | ∃ i ∈ I.map (algebraMap C C'), x * algebraMap C' S' (algebraMap C C' a) = algebraMap C' S' i}
    let θ : C' ⊗[C] ↥B →ₐ[C'] S' :=
      Algebra.TensorProduct.lift (Algebra.ofId C' S') (φ.comp B.val) (fun _ _ => Commute.all _ _)
    Function.Injective θ ∧ ∀ x : S', x ∈ Set.range θ ↔ x ∈ B' := by
  intro B B' θ
  classical
  have hφC : ∀ c : C, φ (algebraMap C S c) = algebraMap C' S' (algebraMap C C' c) := by
    intro c; rw [φ.commutes, IsScalarTower.algebraMap_apply C C' S']
  have hθ : ∀ (c' : C') (b : ↥B), θ (c' ⊗ₜ[C] b) = algebraMap C' S' c' * φ (b : S) :=
    fun c' b => Algebra.TensorProduct.lift_tmul _ _ _ c' b
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := S') (algebraMap C C' a))

  let ψ : C' ⊗[C] S →ₐ[C'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId C' S') φ (fun _ _ => Commute.all _ _)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) (C' ⊗[C] S) :=
    IsLocalization.tensor S (Submonoid.powers a)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) S' := inferInstance
  have hψ : ∀ (c' : C') (s : S), ψ (c' ⊗ₜ[C] s) = algebraMap C' S' c' * φ s :=
    fun c' s => Algebra.TensorProduct.lift_tmul _ _ _ c' s
  let e : C' ⊗[C] S ≃ₐ[C'] S' := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) _ _
  have hψe : ψ = e.toAlgHom :=
    (IsLocalization.algHom_subsingleton (Algebra.algebraMapSubmonoid C' (Submonoid.powers a))).elim _ _
  have hψbij : Function.Bijective ψ := by rw [hψe]; exact e.bijective

  let ι : C' ⊗[C] ↥B →ₐ[C'] C' ⊗[C] S := Algebra.TensorProduct.map (AlgHom.id C' C') B.val
  have hθfac : ∀ t, θ t = ψ (ι t) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c' b =>
      rw [hθ, show ι (c' ⊗ₜ[C] b) = c' ⊗ₜ[C] (b : S) from rfl]
      exact (hψ c' (b : S)).symm
    | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]
  have hιlin : ∀ t, ι t = (B.val.toLinearMap.lTensor C') t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul c' b => rfl
    | add x y hx hy => rw [map_add, hx, hy, map_add]
  have hιinj : Function.Injective ι := by
    have : (ι : C' ⊗[C] ↥B → C' ⊗[C] S) = (B.val.toLinearMap.lTensor C') := funext hιlin
    rw [this]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (fun x y h => Subtype.ext h)
  have hinj : Function.Injective θ := by
    have : (θ : C' ⊗[C] ↥B → S') = ψ ∘ ι := funext hθfac
    rw [this]
    exact hψbij.1.comp hιinj

  have hgen : ∀ x : S, (∃ i ∈ I, x * algebraMap C S a = algebraMap C S i) → φ x ∈ B' := by
    rintro x ⟨i, hi, hx⟩
    apply Algebra.subset_adjoin
    refine ⟨algebraMap C C' i, Ideal.mem_map_of_mem _ hi, ?_⟩
    calc φ x * algebraMap C' S' (algebraMap C C' a) = φ x * φ (algebraMap C S a) := by rw [hφC]
      _ = φ (x * algebraMap C S a) := (map_mul φ _ _).symm
      _ = φ (algebraMap C S i) := by rw [hx]
      _ = algebraMap C' S' (algebraMap C C' i) := hφC i
  have hφB : ∀ y : S, y ∈ B → φ y ∈ B' := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hgen x hx
    | algebraMap c => rw [hφC]; exact Subalgebra.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hsub : ∀ t : C' ⊗[C] ↥B, θ t ∈ B' := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul c' b => rw [hθ]; exact mul_mem (Subalgebra.algebraMap_mem _ _) (hφB _ b.2)
    | add x y hx hy => rw [map_add]; exact add_mem hx hy

  have hcore : ∀ i' : C', i' ∈ I.map (algebraMap C C') → algebraMap C' S' i' * ↑u⁻¹ ∈ Set.range θ := by
    intro i' hi'
    induction hi' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      let xi : S := algebraMap C S i * IsLocalization.Away.invSelf a
      have hxi : xi * algebraMap C S a = algebraMap C S i := by
        show algebraMap C S i * IsLocalization.Away.invSelf a * algebraMap C S a = algebraMap C S i
        rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf a), IsLocalization.Away.mul_invSelf, mul_one]
      have hxiB : xi ∈ B := Algebra.subset_adjoin ⟨i, hi, hxi⟩
      refine ⟨(1 : C') ⊗ₜ[C] ⟨xi, hxiB⟩, ?_⟩
      show θ ((1 : C') ⊗ₜ[C] ⟨xi, hxiB⟩) = _
      rw [hθ, map_one, one_mul, Units.eq_mul_inv_iff_mul_eq, hu]
      calc φ xi * algebraMap C' S' (algebraMap C C' a) = φ xi * φ (algebraMap C S a) := by rw [hφC]
        _ = φ (xi * algebraMap C S a) := (map_mul φ _ _).symm
        _ = φ (algebraMap C S i) := by rw [hxi]
        _ = algebraMap C' S' (algebraMap C C' i) := hφC i
    | zero => exact ⟨0, by rw [map_zero, map_zero, zero_mul]⟩
    | add z w _ _ hz hw =>
      obtain ⟨tz, htz⟩ := hz
      obtain ⟨tw, htw⟩ := hw
      exact ⟨tz + tw, by rw [map_add, htz, htw, map_add, add_mul]⟩
    | smul c z _ hz =>
      obtain ⟨tz, htz⟩ := hz
      exact ⟨c • tz, by rw [map_smul, htz, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc]⟩
  have hsup : ∀ x : S', x ∈ B' → x ∈ Set.range θ := by
    intro x hx
    have hR : (θ.range : Set S') = Set.range θ := rfl
    rw [← hR]
    refine Algebra.adjoin_le ?_ hx
    rintro y ⟨i', hi', hy⟩
    have hy' : y = algebraMap C' S' i' * ↑u⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq, hu]; exact hy
    rw [hy']
    exact hcore i' hi'
  exact ⟨hinj, fun x => ⟨fun ⟨t, ht⟩ => ht ▸ hsub t, hsup x⟩⟩

end S_Algebra_adjoin_div_tensorProduct_bijective_of_flat
end P2MW
export P2MW.S_Algebra_adjoin_div_tensorProduct_bijective_of_flat (solution)
