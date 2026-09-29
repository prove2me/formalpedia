-- Prove2me | solution 1 for AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/4beb41fa-7f60-5599-b5ce-ec726ffca5aa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot

set_option autoImplicit false

universe u

theorem solution
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    (C : Type u) [CommRing C] [Algebra T' C]
    (ψ : C →ₐ[T'] C) (hψ : ∀ c : C, ψ c - c ∈ I.map (algebraMap T' C)) :
    Function.Bijective ψ ∧ ∀ p : PrimeSpectrum C, PrimeSpectrum.comap ψ.toRingHom p = p := by
  classical
  set J : Ideal C := I.map (algebraMap T' C) with hJ
  have hJJ : J * J = ⊥ := by rw [hJ, ← Ideal.map_mul, hI2, Ideal.map_bot]
  have hmul0 : ∀ y ∈ J, ∀ z ∈ J, y * z = 0 := fun y hy z hz => by
    have := Ideal.mul_mem_mul hy hz; rwa [hJJ, Ideal.mem_bot] at this

  have hfix : ∀ y ∈ J, ψ y = y := by
    intro y hy
    rw [hJ, Ideal.map] at hy
    refine Submodule.span_induction (p := fun y _ => ψ y = y) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨i, hi, rfl⟩
      exact ψ.commutes i
    · exact map_zero ψ
    · intro y z _ _ hy hz
      rw [map_add, hy, hz]
    · intro c y hy' hy
      have hyJ : y ∈ J := by rw [hJ, Ideal.map]; exact hy'
      rw [smul_eq_mul, map_mul, hy, ← sub_eq_zero, ← sub_mul]
      exact hmul0 _ (hψ c) _ hyJ
  refine ⟨?_, ?_⟩
  ·
    refine Function.bijective_iff_has_inverse.mpr ⟨fun c => c - (ψ c - c), fun c => ?_, fun c => ?_⟩
    · show ψ c - (ψ (ψ c) - ψ c) = c
      have : ψ (ψ c) = ψ c + (ψ c - c) := by
        conv_lhs => rw [show ψ c = c + (ψ c - c) by abel]
        rw [map_add, hfix _ (hψ c)]
      rw [this]; abel
    · show ψ (c - (ψ c - c)) = c
      rw [map_sub, hfix _ (hψ c)]; abel
  · intro p
    apply PrimeSpectrum.ext
    ext c
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
    have hnil : ψ c - c ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [pow_two, hmul0 _ (hψ c) _ (hψ c)]
      exact p.asIdeal.zero_mem
    constructor
    · intro h
      have := p.asIdeal.sub_mem h hnil
      rwa [show (ψ.toRingHom c) - (ψ c - c) = c from by simp] at this
    · intro h
      have := p.asIdeal.add_mem h hnil
      rwa [show c + (ψ c - c) = ψ.toRingHom c from by simp] at this

end S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot
end P2MW
export P2MW.S_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot (solution)
