-- Prove2me | solution 1 for AlgEquiv.apply_eq_inv_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/bc02d4af-a5df-54e2-b1f3-6c6d82b1173c

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgEquiv_apply_eq_inv_of_pow_eq_one

namespace AlgEquiv
p2m_export "AlgEquiv" "ext mul_apply trans symm one_apply"
p2m_open "AlgEquiv"

namespace InvolutionAux

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [CharZero K]
  (c : K ≃ₐ[F] K)

omit [IsAlgClosed K] [CharZero K] in
theorem apply_apply_of_mul_self (hc : c * c = 1) (x : K) : c (c x) = x := by
  rw [← AlgEquiv.mul_apply, hc, AlgEquiv.one_apply]

omit [CharZero K] in
theorem exists_sq_eq (x : K) : ∃ w : K, w ^ 2 = x :=
  IsAlgClosed.exists_pow_nat_eq x two_pos

omit [IsAlgClosed K] in
theorem ne_neg_self_of_sq_eq_neg_one {i : K} (hi : i ^ 2 = -1) : i ≠ -i := by
  intro h
  have h0 : i = 0 := by
    have h2 : (2 : K) * i = 0 := by rw [two_mul]; nth_rw 2 [h]; exact add_neg_cancel i
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero
  rw [h0] at hi
  norm_num at hi

theorem apply_eq_neg_of_sq_eq_neg_one (hc : c * c = 1) (hc1 : c ≠ 1) {i : K} (hi : i ^ 2 = -1) :
    c i = -i := by
  have hcc := apply_apply_of_mul_self c hc
  have hci : c i = i ∨ c i = -i := by
    rw [← sq_eq_sq_iff_eq_or_eq_neg, ← map_pow, hi, map_neg, map_one]
  refine hci.resolve_left fun hfix => hc1 ?_

  ext z
  by_contra hz
  set u := z - c z with hu
  have hu0 : u ≠ 0 := fun h => hz (sub_eq_zero.mp h).symm
  have hcu : c u = -u := by rw [hu, map_sub, hcc, neg_sub]
  obtain ⟨β, hβ⟩ := exists_sq_eq u
  have hcβ : c β = i * β ∨ c β = -(i * β) := by
    rw [← sq_eq_sq_iff_eq_or_eq_neg, ← map_pow, hβ, hcu, mul_pow, hi, ← hβ]; ring
  have hβ0 : β ≠ 0 := by rintro rfl; exact hu0 (by rw [← hβ]; ring)
  have key : c (c β) = -β := by
    rcases hcβ with h | h
    · rw [h, map_mul, hfix, h, ← mul_assoc, ← sq, hi]; ring
    · rw [h, map_neg, map_mul, hfix, h, mul_neg, ← mul_assoc, ← sq, hi]; ring
  rw [hcc] at key
  exact hβ0 (by
    have h2 : (2 : K) * β = 0 := by rw [two_mul]; nth_rw 2 [key]; exact add_neg_cancel β
    exact (mul_eq_zero.mp h2).resolve_left two_ne_zero)

theorem exists_sq_add_sq_eq_sq (hc : c * c = 1) (hc1 : c ≠ 1) {x y : K} (hx : c x = x)
    (hy : c y = y) : ∃ z : K, c z = z ∧ x ^ 2 + y ^ 2 = z ^ 2 := by
  have hcc := apply_apply_of_mul_self c hc
  obtain ⟨i, hi⟩ := exists_sq_eq (-1 : K)
  have hci := apply_eq_neg_of_sq_eq_neg_one c hc hc1 hi
  obtain ⟨w, hw⟩ := exists_sq_eq (x + i * y)
  refine ⟨w * c w, by rw [map_mul, hcc, mul_comm], ?_⟩
  calc x ^ 2 + y ^ 2 = (x + i * y) * c (x + i * y) := by
        rw [map_add, map_mul, hx, hy, hci]; linear_combination (y ^ 2) * hi
    _ = (w * c w) ^ 2 := by rw [← hw, map_pow]; ring

theorem eq_zero_of_sq_add_sq_eq_zero (hc : c * c = 1) (hc1 : c ≠ 1) {x y : K} (hx : c x = x)
    (hy : c y = y) (h : x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  obtain ⟨i, hi⟩ := exists_sq_eq (-1 : K)
  have hci := apply_eq_neg_of_sq_eq_neg_one c hc hc1 hi
  have hii := ne_neg_self_of_sq_eq_neg_one (K := K) hi
  suffices hy0 : y = 0 by
    subst hy0
    exact ⟨eq_zero_of_pow_eq_zero (n := 2) (by simpa using h), rfl⟩
  by_contra hy0
  have hq : (x / y) ^ 2 = i ^ 2 := by
    rw [hi, div_pow, div_eq_iff (pow_ne_zero 2 hy0)]; linear_combination h
  have hcq : c (x / y) = x / y := by rw [map_div₀, hx, hy]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq with hq | hq
  · rw [hq, hci] at hcq; exact hii hcq.symm
  · rw [hq, map_neg, hci, neg_neg] at hcq; exact hii hcq

theorem sum_sq_eq_zero_iff (hc : c * c = 1) (hc1 : c ≠ 1) (x : ℕ → K) (m : ℕ)
    (hx : ∀ j < m, c (x j) = x j) :
    (∃ z : K, c z = z ∧ ∑ j ∈ Finset.range m, x j ^ 2 = z ^ 2) ∧
      (∑ j ∈ Finset.range m, x j ^ 2 = 0 → ∀ j < m, x j = 0) := by
  induction m with
  | zero => exact ⟨⟨0, by simp, by simp⟩, fun _ j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ m ih =>
    obtain ⟨⟨z, hz, hsum⟩, ih0⟩ := ih fun j hj => hx j (Nat.lt_succ_of_lt hj)
    have hxm : c (x m) = x m := hx m (Nat.lt_succ_self m)
    refine ⟨?_, fun h0 j hj => ?_⟩
    · obtain ⟨z', hz', h'⟩ := exists_sq_add_sq_eq_sq c hc hc1 hz hxm
      exact ⟨z', hz', by rw [Finset.sum_range_succ, hsum, h']⟩
    · rw [Finset.sum_range_succ, hsum] at h0
      obtain ⟨hz0, hxm0⟩ := eq_zero_of_sq_add_sq_eq_zero c hc hc1 hz hxm h0
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · refine ih0 ?_ j hj
        rw [hsum, hz0]; ring
      · exact hxm0

theorem eq_one_of_pow_odd_eq_one (hc : c * c = 1) (hc1 : c ≠ 1) {r : K} (hr : c r = r) {d : ℕ}
    (hd : Odd d) (hrd : r ^ d = 1) : r = 1 := by
  by_contra hr1

  set u := r ^ ((d + 1) / 2) with hu
  have hur : u ^ 2 = r := by
    rw [hu, ← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.mp hd.add_one), pow_succ, hrd,
      one_mul]
  have hcu : ∀ j, c (u ^ j) = u ^ j := fun j => by rw [map_pow, hu, map_pow, hr]

  have hgeom : ∑ j ∈ Finset.range d, (u ^ j) ^ 2 = 0 := by
    have : ∑ j ∈ Finset.range d, r ^ j = 0 := by
      rw [geom_sum_eq hr1, hrd, sub_self, zero_div]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by rw [← pow_mul, mul_comm, pow_mul, hur]
  have h0 := (sum_sq_eq_zero_iff c hc hc1 (fun j => u ^ j) d fun j _ => hcu j).2 hgeom 0 hd.pos
  simp at h0

theorem eq_or_eq_neg_of_pow_two_pow_eq_one (hc : c * c = 1) (hc1 : c ≠ 1) {t : K}
    (ht : c t = t) {a : ℕ} (hta : t ^ 2 ^ a = 1) : t = 1 ∨ t = -1 := by
  induction a generalizing t with
  | zero => exact Or.inl (by simpa using hta)
  | succ a ih =>
    have h2 : (t ^ 2) ^ 2 ^ a = 1 := by rwa [← pow_mul, ← pow_succ']
    rcases ih (by rw [map_pow, ht]) h2 with h | h
    · exact sq_eq_sq_iff_eq_or_eq_neg.mp (by rwa [one_pow])
    · exfalso

      exact ne_neg_self_of_sq_eq_neg_one (K := K) h
        ((apply_eq_neg_of_sq_eq_neg_one c hc hc1 h).symm.trans ht).symm

theorem eq_or_eq_neg_of_pow_eq_one (hc : c * c = 1) (hc1 : c ≠ 1) {t : K} (ht : c t = t)
    {m : ℕ} (hm : m ≠ 0) (htm : t ^ m = 1) : t = 1 ∨ t = -1 := by
  obtain ⟨a, d, hd, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hm
  refine eq_or_eq_neg_of_pow_two_pow_eq_one c hc hc1 ht (a := a) ?_
  exact eq_one_of_pow_odd_eq_one c hc hc1 (by rw [map_pow, ht]) hd (by rwa [← pow_mul])

end InvolutionAux

open InvolutionAux in

theorem apply_eq_inv_of_pow_eq_one' {F K : Type*} [Field F] [Field K] [Algebra F K]
    [IsAlgClosed K] [CharZero K] (c : K ≃ₐ[F] K) (hc : c * c = 1) (hc1 : c ≠ 1) {ζ : K} {n : ℕ}
    (hn : n ≠ 0) (hζ : ζ ^ n = 1) : c ζ = ζ⁻¹ := by
  have hcc := apply_apply_of_mul_self c hc
  have hζ0 : ζ ≠ 0 := by rintro rfl; exact zero_ne_one ((zero_pow hn).symm.trans hζ)
  obtain ⟨w, hw⟩ := exists_sq_eq ζ

  have ht : c (w * c w) = w * c w := by rw [map_mul, hcc, mul_comm]
  have h2 : (w * c w) ^ 2 = ζ * c ζ := by rw [mul_pow, ← map_pow, hw]
  have htn : (w * c w) ^ (2 * n) = 1 := by
    rw [pow_mul, h2, mul_pow, ← map_pow, hζ, map_one, one_mul]
  have ht1 : (w * c w) ^ 2 = 1 := by
    rcases eq_or_eq_neg_of_pow_eq_one c hc hc1 ht (by positivity) htn with h | h <;>
      rw [h] <;> norm_num
  exact (inv_eq_of_mul_eq_one_right (h2.symm.trans ht1)).symm

end AlgEquiv

theorem solution {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [CharZero K] (c : K ≃ₐ[F] K) (hc : c * c = 1) (hc1 : c ≠ 1) {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) : c ζ = ζ⁻¹ :=
  AlgEquiv.apply_eq_inv_of_pow_eq_one' c hc hc1 hn hζ

end S_AlgEquiv_apply_eq_inv_of_pow_eq_one
end P2MW
export P2MW.S_AlgEquiv_apply_eq_inv_of_pow_eq_one (solution)
