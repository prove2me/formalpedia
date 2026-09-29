-- Prove2me | solution 1 for Algebra.TensorProduct.nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/74ca9f58-f8e3-5ce3-9414-a6ba87fdc63c

import Mathlib
import Theorems.Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range

set_option autoImplicit false

open scoped TensorProduct

namespace P2mGeomIrred

variable {K L Ω : Type*} [Field K] [Field L] [Field Ω] [Algebra K L] [Algebra K Ω]

set_option backward.isDefEq.respectTransparency false in

theorem main [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime := by
  classical
  obtain ⟨q, hq⟩ := ExpChar.exists K
  set Ωs : IntermediateField K Ω := separableClosure K Ω with hΩs

  have hF : IsField (L ⊗[K] Ωs) :=
    Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range K L Ωs hsc
  letI : Field (L ⊗[K] Ωs) := hF.toField

  let ι : L ⊗[K] Ωs →ₐ[K] L ⊗[K] Ω := Algebra.TensorProduct.map (AlgHom.id K L) Ωs.val
  have hι : Function.Injective ι := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L)
      (Ωs.val.toLinearMap) Subtype.val_injective
    intro a b hab
    apply h
    change ι a = ι b
    exact hab

  haveI : Nontrivial (L ⊗[K] Ω) :=
    (Algebra.TensorProduct.includeLeft_injective (R := K) (A := L) (B := Ω) (S := K)
      (algebraMap K Ω).injective).nontrivial
  haveI : ExpChar (L ⊗[K] Ω) q :=
    expChar_of_injective_algebraMap (algebraMap K (L ⊗[K] Ω)).injective q

  have hmono : ∀ (t : L ⊗[K] Ω) (n m : ℕ), t ^ q ^ n ∈ ι.range → t ^ q ^ (n + m) ∈ ι.range := by
    intro t n m ht
    have : t ^ q ^ (n + m) = (t ^ q ^ n) ^ q ^ m := by rw [← pow_mul, ← pow_add]
    rw [this]
    exact pow_mem ht _
  have hpow : ∀ t : L ⊗[K] Ω, ∃ n : ℕ, t ^ q ^ n ∈ ι.range := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l ω =>
      obtain ⟨n, y, hy⟩ := (isPurelyInseparable_iff_pow_mem Ωs q).mp inferInstance ω
      refine ⟨n, (l ^ q ^ n) ⊗ₜ[K] y, ?_⟩
      change ι ((l ^ q ^ n) ⊗ₜ[K] y) = _
      rw [Algebra.TensorProduct.tmul_pow]
      simp only [ι, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
      congr 1
    | add a b ha hb =>
      obtain ⟨n, ha⟩ := ha
      obtain ⟨m, hb⟩ := hb
      refine ⟨n + m, ?_⟩
      rw [add_pow_expChar_pow]
      refine add_mem (hmono a n m ha) ?_
      rw [add_comm n m]
      exact hmono b m n hb

  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : (1 : L ⊗[K] Ω) ∈ nilradical (L ⊗[K] Ω) := htop ▸ Submodule.mem_top
    rw [mem_nilradical] at h1
    obtain ⟨N, hN⟩ := h1
    rw [one_pow] at hN
    exact one_ne_zero hN
  · intro a b hab
    rw [mem_nilradical] at hab
    obtain ⟨N, hN⟩ := hab
    obtain ⟨n, α, hα⟩ := hpow a
    obtain ⟨m, β, hβ⟩ := hpow b
    replace hα : ι α = a ^ q ^ n := hα
    replace hβ : ι β = b ^ q ^ m := hβ
    have hα' : ι (α ^ q ^ m) = a ^ q ^ (n + m) := by
      rw [map_pow, hα, ← pow_mul, ← pow_add]
    have hβ' : ι (β ^ q ^ n) = b ^ q ^ (n + m) := by
      rw [map_pow, hβ, ← pow_mul, ← pow_add, add_comm]
    have h0 : (α ^ q ^ m * β ^ q ^ n) ^ N = 0 := by
      apply hι
      rw [map_pow, map_mul, hα', hβ', ← mul_pow, ← pow_mul, mul_comm (q ^ (n + m)) N, pow_mul,
        hN, zero_pow (pow_ne_zero _ (expChar_pos K q).ne'), map_zero]
    have h1 : α ^ q ^ m * β ^ q ^ n = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rcases mul_eq_zero.mp h1 with h | h
    · left
      rw [mem_nilradical]
      refine ⟨q ^ (n + m), ?_⟩
      rw [← hα', h, map_zero]
    · right
      rw [mem_nilradical]
      refine ⟨q ^ (n + m), ?_⟩
      rw [← hβ', h, map_zero]

end P2mGeomIrred

universe u v w

theorem solution
    (K : Type u) (L : Type v) (Ω : Type w) [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (hsc : ∀ y : L, IsSeparable K y → y ∈ (algebraMap K L).range) :
    (nilradical (L ⊗[K] Ω)).IsPrime :=
  P2mGeomIrred.main hsc

end S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range
end P2MW
export P2MW.S_Algebra_TensorProduct_nilradical_isPrime_of_isAlgebraic_of_forall_isSeparable_mem_range (solution)
