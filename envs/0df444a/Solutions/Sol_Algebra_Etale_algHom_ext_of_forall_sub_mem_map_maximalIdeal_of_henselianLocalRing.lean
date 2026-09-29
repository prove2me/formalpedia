-- Prove2me | solution 1 for Algebra.Etale.algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5e4bc487-b9f6-57eb-838a-cea1e46b7aa6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem solution
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E : Type v) [CommRing E] [Algebra R E] [Module.Finite R E] [Algebra.Etale R E]
    (B : Type w) [CommRing B] [Algebra R B] [Module.Finite R B]
    (φ ψ : E →ₐ[R] B)
    (h : ∀ x : E, φ x - ψ x ∈ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :
    φ = ψ := by
  classical
  set I : Ideal B := Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) with hI

  have hIJ : I ≤ Ideal.jacobson (⊥ : Ideal B) := by
    refine le_sInf fun J hJ => ?_
    obtain ⟨-, hJmax⟩ := hJ
    rw [hI, Ideal.map_le_iff_le_comap]
    have hc : (J.comap (algebraMap R B)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
    rw [← IsLocalRing.eq_maximalIdeal hc]

  set e : E ⊗[R] E := Algebra.FormallyUnramified.elem R E with he
  have he1 : ∀ s : E, ((1 : E) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : E)) * e = 0 :=
    fun s => Algebra.FormallyUnramified.one_tmul_sub_tmul_one_mul_elem s
  have he2 : Algebra.TensorProduct.lmul' R e = 1 := Algebra.FormallyUnramified.lmul_elem
  set Φ : E ⊗[R] E →ₐ[R] B := Algebra.TensorProduct.productMap φ ψ with hΦ

  have hΦμ : ∀ t : E ⊗[R] E, Φ t - φ (Algebra.TensorProduct.lmul' R t) ∈ I := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
        rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul, map_mul,
          ← mul_sub]
        refine I.mul_mem_left _ ?_
        have := I.neg_mem (h b)
        rwa [neg_sub] at this
    | add u v hu hv =>
        rw [map_add, map_add, map_add]
        convert I.add_mem hu hv using 1
        ring
  have hΦe : Φ e - 1 ∈ Ideal.jacobson (⊥ : Ideal B) := by
    apply hIJ
    simpa [he2] using hΦμ e
  have hunit : IsUnit (Φ e) := Ideal.isUnit_of_sub_one_mem_jacobson_bot _ hΦe

  refine AlgHom.ext fun x => ?_
  have hdx : Φ (x ⊗ₜ[R] 1 - 1 ⊗ₜ[R] x) = φ x - ψ x := by
    rw [map_sub, hΦ, Algebra.TensorProduct.productMap_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul,
      map_one, map_one, mul_one, one_mul]
  have hann : (x ⊗ₜ[R] (1 : E) - (1 : E) ⊗ₜ[R] x) * e = 0 := by
    rw [← neg_sub, neg_mul, he1 x, neg_zero]
  have hkey : (φ x - ψ x) * Φ e = 0 := by
    rw [← hdx, ← map_mul, hann, map_zero]
  exact sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hkey)

end S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing
end P2MW
export P2MW.S_Algebra_Etale_algHom_ext_of_forall_sub_mem_map_maximalIdeal_of_henselianLocalRing (solution)
