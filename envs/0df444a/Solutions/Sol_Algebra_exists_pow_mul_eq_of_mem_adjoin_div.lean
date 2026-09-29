-- Prove2me | solution 1 for Algebra.exists_pow_mul_eq_of_mem_adjoin_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/92c05f28-5684-5db1-9786-b96f140e071a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div

set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
    (I : Ideal R) (a : R) (ha : a ∈ I) (x : S)
    (hx : x ∈ Algebra.adjoin R {x : S | ∃ i ∈ I, x * algebraMap R S a = algebraMap R S i}) :
    ∃ (n : ℕ) (c : R), c ∈ I ^ n ∧ x * algebraMap R S a ^ n = algebraMap R S c := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, hi, hxi⟩ := hx
    exact ⟨1, i, by simpa using hi, by simpa using hxi⟩
  | algebraMap r => exact ⟨0, r, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, c, hc, hxc⟩ := hx
    obtain ⟨m, d, hd, hyd⟩ := hy
    refine ⟨n + m, c * a ^ m + d * a ^ n, ?_, ?_⟩
    · refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hc (Ideal.pow_mem_pow ha m)
      · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hd (Ideal.pow_mem_pow ha n)
    · rw [add_mul, map_add, map_mul, map_mul, map_pow, map_pow, ← hxc, ← hyd]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨n, c, hc, hxc⟩ := hx
    obtain ⟨m, d, hd, hyd⟩ := hy
    refine ⟨n + m, c * d, ?_, ?_⟩
    · rw [pow_add]; exact Ideal.mul_mem_mul hc hd
    · rw [map_mul, ← hxc, ← hyd]; ring

end S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div
end P2MW
export P2MW.S_Algebra_exists_pow_mul_eq_of_mem_adjoin_div (solution)
