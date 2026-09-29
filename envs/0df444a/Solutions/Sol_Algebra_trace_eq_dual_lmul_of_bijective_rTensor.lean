-- Prove2me | solution 1 for Algebra.trace_eq_dual_lmul_of_bijective_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/3c8bf5ed-c2cb-5a37-9afb-32a9853500c9

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor

set_option autoImplicit false

open scoped TensorProduct

namespace Ws23
namespace CoreD

open Module
open scoped TensorProduct

variable (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]

theorem lid_rTensor_sum (φ : Dual R A) (S : Finset (A × A)) :
    TensorProduct.lid R A (LinearMap.rTensor A φ (∑ p ∈ S, p.1 ⊗ₜ[R] p.2)) = ∑ p ∈ S, φ p.1 • p.2 := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]

theorem main [Module.Finite R A] [Module.Free R A]
    (τ : Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) := by
  classical

  obtain ⟨S, hS⟩ := TensorProduct.exists_finset Δ

  have hone : ∑ p ∈ S, τ p.1 • p.2 = 1 := by rw [← lid_rTensor_sum R A τ S, ← hS, hτ]
  have key : ∀ a : A, ∑ p ∈ S, τ (a * p.1) • p.2 = a := by
    intro a
    have hl : (a ⊗ₜ[R] (1 : A)) * Δ = ∑ p ∈ S, (a * p.1) ⊗ₜ[R] p.2 := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have hr : ((1 : A) ⊗ₜ[R] a) * Δ = ∑ p ∈ S, p.1 ⊗ₜ[R] (a * p.2) := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    have h := congrArg (fun z => TensorProduct.lid R A (LinearMap.rTensor A τ z)) (hbal a)
    simp only [hl, hr, map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at h
    rw [h]
    calc ∑ p ∈ S, τ p.1 • (a * p.2) = a * ∑ p ∈ S, τ p.1 • p.2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_smul_comm]
      _ = a := by rw [hone, mul_one]

  have hlmul : Algebra.lmul R A x =
      dualTensorHom R A A (∑ p ∈ S, (τ.comp (LinearMap.mulLeft R (x * p.1))) ⊗ₜ[R] p.2) := by
    apply LinearMap.ext
    intro m
    rw [map_sum, LinearMap.sum_apply]
    simp only [dualTensorHom_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
    have := key (x * m)
    calc Algebra.lmul R A x m = x * m := rfl
      _ = ∑ p ∈ S, τ (x * m * p.1) • p.2 := this.symm
      _ = ∑ p ∈ S, τ (x * p.1 * m) • p.2 := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [mul_right_comm]

  rw [Algebra.trace_apply, hlmul, LinearMap.trace_eq_contract_apply, map_sum]
  simp only [contractLeft_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply]
  rw [← map_sum]
  congr 1
  rw [hS, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [LinearMap.mul'_apply]
  ring

end Ws23.CoreD

theorem solution
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A] [Module.Finite R A] [Module.Free R A]
    (τ : Module.Dual R A) (Δ : A ⊗[R] A)
    (hbal : ∀ s : A, (s ⊗ₜ[R] (1 : A)) * Δ = ((1 : A) ⊗ₜ[R] s) * Δ)
    (hbij : Function.Bijective (fun φ : Module.Dual R A => TensorProduct.lid R A (LinearMap.rTensor A φ Δ)))
    (hτ : TensorProduct.lid R A (LinearMap.rTensor A τ Δ) = 1) (x : A) :
    Algebra.trace R A x = τ (LinearMap.mul' R A Δ * x) :=
  Ws23.CoreD.main R A τ Δ hbal hτ x

end S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor
end P2MW
export P2MW.S_Algebra_trace_eq_dual_lmul_of_bijective_rTensor (solution)
