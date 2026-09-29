-- Prove2me | solution 1 for Algebra.IsPushout.exists_algHom_slice_eq_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/dbe12ffe-1868-58a6-ad48-699b633e105f

import Mathlib
import Theorems.Thm_Algebra_IsPushout_slice_ext_and_exists_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_IsPushout_exists_algHom_slice_eq_of_flat

set_option autoImplicit false

open TensorProduct

universe u

theorem solution
    {B B₁ B' M N : Type u} [CommRing B] [CommRing B₁] [CommRing B'] [CommRing M] [CommRing N]
    [Algebra B B₁] [Algebra B' B₁] [Algebra B B'] [Algebra B M] [Algebra B' N] [Algebra M N] [Algebra B N]
    [IsScalarTower B B' N] [IsScalarTower B M N] [Algebra.IsPushout B B' M N] [Module.Flat B M]
    (hπ : Function.Surjective (algebraMap B B₁))
    (p : Fin 3 → (B' →ₐ[B] B))
    (hp : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (p i x) = algebraMap B' B₁ x)
    (hinj : ∀ x y : B', (∀ i, p i x = p i y) → x = y)
    (hsurj : ∀ b : Fin 3 → B, (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) → ∃ x : B', ∀ i, p i x = b i)
    (e : Fin 3 → (N →ₐ[B] M))
    (heM : ∀ (i : Fin 3) (m : M), e i (algebraMap M N m) = m)
    (heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' N x) = algebraMap B M (p i x))
    (t : Fin 3 → (M →ₐ[B] M))
    (ht : ∀ (i : Fin 3) (m : M), t i m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)) :
    ∃ σ : N →ₐ[B'] N,
      (∀ (i : Fin 3) (n : N), e i (σ n) = t i (e i n)) ∧
      (∀ n : N, σ n - n ∈ (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)) ∧
      (∀ σ' : N →ₐ[B'] N, (∀ (i : Fin 3) (n : N), e i (σ' n) = t i (e i n)) → ∀ n : N, σ' n = σ n) := by
  classical
  obtain ⟨hinjN, hsurjN⟩ := Algebra.IsPushout.slice_ext_and_exists_of_flat (B := B) (B₁ := B₁) (B' := B') (M := M) (N := N)
    hπ p hp hinj hsurj e heM heB
  let J : Ideal M := (RingHom.ker (algebraMap B B₁)).map (algebraMap B M)
  let J' : Ideal N := (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' N)
  have hJt : ∀ (i : Fin 3) (m : M), m ∈ J → t i m ∈ J := by
    intro i m hm
    have : J.map (t i : M →+* M) ≤ J := by
      rw [Ideal.map_map]
      have : (t i : M →+* M).comp (algebraMap B M) = algebraMap B M := RingHom.ext fun b => (t i).commutes b
      rw [this]
    exact this (Ideal.mem_map_of_mem _ hm)
  have hcong : ∀ (n : N) (i j : Fin 3), e i n - e j n ∈ J := by
    haveI : Algebra.IsPushout B M B' N := Algebra.IsPushout.symm inferInstance
    intro n i j
    obtain ⟨x, rfl⟩ := (Algebra.IsPushout.equiv B M B' N).surjective n
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      rw [Algebra.IsPushout.equiv_tmul, map_mul, map_mul, heM, heM, heB, heB, ← mul_sub, ← map_sub]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker, map_sub, hp, hp, sub_self]
    | add x y hx hy =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact J.add_mem hx hy
  have hex : ∀ n : N, ∃ n' : N, ∀ i, e i n' = t i (e i n) := by
    intro n
    refine hsurjN (fun i => t i (e i n)) (fun i j => ?_)
    have : t i (e i n) - t j (e j n) = (t i (e i n) - e i n) + (e i n - e j n) - (t j (e j n) - e j n) := by ring
    rw [this]
    exact J.sub_mem (J.add_mem (ht i _) (hcong n i j)) (ht j _)
  choose f hf using hex
  let σ : N →ₐ[B'] N :=
    { toFun := f
      map_one' := hinjN _ _ fun i => by rw [hf, map_one, map_one]
      map_mul' := fun x y => hinjN _ _ fun i => by rw [hf, map_mul, map_mul, map_mul, hf, hf]
      map_zero' := hinjN _ _ fun i => by rw [hf, map_zero, map_zero]
      map_add' := fun x y => hinjN _ _ fun i => by rw [hf, map_add, map_add, map_add, hf, hf]
      commutes' := fun x => hinjN _ _ fun i => by rw [hf, heB, AlgHom.commutes] }
  have hσ : ∀ i n, e i (σ n) = t i (e i n) := fun i n => hf n i
  refine ⟨σ, hσ, ?_, ?_⟩
  · have hsingle : ∀ (k : Fin 3) (d : M), d ∈ J → ∃ n : N, n ∈ J' ∧ ∀ i, e i n = (Pi.single k d : Fin 3 → M) i := by
      intro k d hd
      refine Submodule.span_induction (p := fun d _ => ∃ n : N, n ∈ J' ∧ ∀ i, e i n = (Pi.single k d : Fin 3 → M) i) ?_ ?_ ?_ ?_ hd
      · rintro _ ⟨j, hj, rfl⟩
        have hj0 : algebraMap B B₁ j = 0 := hj
        obtain ⟨x, hx⟩ := hsurj (Pi.single k j : Fin 3 → B) (fun i i' => by
          simp only [Pi.single_apply]
          split_ifs <;> simp [hj0])
        refine ⟨algebraMap B' N x, Ideal.mem_map_of_mem _ ?_, fun i => ?_⟩
        · rw [RingHom.mem_ker, ← hp 0, hx, Pi.single_apply]
          split_ifs <;> simp [hj0]
        · rw [heB, hx, Pi.single_apply, Pi.single_apply]
          split_ifs <;> simp
      · exact ⟨0, J'.zero_mem, fun i => by simp⟩
      · rintro d₁ d₂ _ _ ⟨n₁, hn₁J, hn₁⟩ ⟨n₂, hn₂J, hn₂⟩
        exact ⟨n₁ + n₂, J'.add_mem hn₁J hn₂J, fun i => by rw [map_add, hn₁, hn₂, Pi.single_add, Pi.add_apply]⟩
      · rintro c d _ ⟨n, hnJ, hn⟩
        refine ⟨algebraMap M N c * n, J'.mul_mem_left _ hnJ, fun i => ?_⟩
        rw [map_mul, heM, hn, Pi.single_apply, Pi.single_apply, smul_eq_mul]
        split_ifs <;> simp
    intro n
    change σ n - n ∈ J'
    obtain ⟨n₀, hn₀J, hn₀⟩ := hsingle 0 _ (ht 0 (e 0 n))
    obtain ⟨n₁, hn₁J, hn₁⟩ := hsingle 1 _ (ht 1 (e 1 n))
    obtain ⟨n₂, hn₂J, hn₂⟩ := hsingle 2 _ (ht 2 (e 2 n))
    have : σ n - n = n₀ + n₁ + n₂ := hinjN _ _ fun i => by
      rw [map_sub, hσ, map_add, map_add, hn₀, hn₁, hn₂]
      fin_cases i <;> simp
    rw [this]
    exact J'.add_mem (J'.add_mem hn₀J hn₁J) hn₂J
  · intro σ'' hσ'' n
    exact hinjN _ _ fun i => by rw [hσ'', hσ]

end S_Algebra_IsPushout_exists_algHom_slice_eq_of_flat
end P2MW
export P2MW.S_Algebra_IsPushout_exists_algHom_slice_eq_of_flat (solution)
