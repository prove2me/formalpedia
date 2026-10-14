-- Prove2me | solution 1 for Apery.small_range_le
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-12T14:22:38.019386+00:00
-- url     : https://prove2.me/submissions/beaa8b6c-66f2-46fb-be27-2a0f0156c4c4

/-
# Irrationality of $\zeta(5)$ via normalized Hankel determinants
# The small-prime range of $\log m_K$ (source `Apery/Growth/Assembly1.lean`)

This file proves the platform theorem `Apery.small_range_le`: for `n ≥ 1`,

$$\sum_{k \le n/10} c(k)\,\bigl(-L_k\bigr) \;\le\;
  6\cdot 37n\,\Bigl(\theta\bigl(\tfrac{n}{10}\bigr) + \bigl(\sqrt{200n}+1\bigr)\log(200n)\Bigr)
  + 37n\cdot 100,$$

where $c(k) = \log k$ for primes and $0$ otherwise, $\theta$ is Chebyshev's function, and
$L_k$ is the small-prime exponent (3.12) of the normaliser `mN`. The estimate uses only
$\theta(M) \le \sum_{k\le M} c(k)$ and elementary comparisons; it is independent of the
prime number theorem. A faithful port of the pinned source project
mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0, `Apery/Growth/Assembly1.lean`
(and `theta_eq_sum_cPrime` from `Apery/PrimeSum.lean`).
-/

import Mathlib
import Definitions.Def_Zeta5_SourceNorm
import Definitions.Def_Zeta5_SourcePrimeSum

set_option autoImplicit false

section Port0
/-!
# The small-prime range of `log m_K`

The bound `Apery.small_range_le` of the growth chain: for `n ≥ 1`,

`∑_{k ≤ n/10} cPrime k * (-Lp n k) ≤
   6 · 37n · (θ(n/10) + (√(200n) + 1) log(200n)) + 37n · 100`,

where `θ` is Chebyshev's function and `cPrime k = log k` for primes, `0` otherwise.

Ported from mo271/Zeta5 @ 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Growth/Assembly1.lean` (lemmas `log_mul_natLog_le`, `cPrime_natLog_le`,
`sum_cPrime_le_theta`, `cPrime_nonneg'`, `small_range_le`; the auxiliary
`theta_eq_sum_cPrime` is from `Apery/PrimeSum.lean`). The estimate uses only
`θ ≤ ∑_{k ≤ M} cPrime k` and elementary comparisons; it is independent of the
prime number theorem.
-/

open Finset

namespace Apery

/-- `θ(t) = ∑_{k ≤ ⌊t⌋} cPrime k`. -/
lemma theta_eq_sum_cPrime (t : ℝ) : Chebyshev.theta t = ∑ k ∈ Icc 0 ⌊t⌋₊, cPrime k := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

lemma log_mul_natLog_le {k Z : ℕ} (hk : 2 ≤ k) (hZ : 1 ≤ Z) :
    (Nat.log k Z : ℝ) * Real.log k ≤ Real.log Z := by
  have h := Nat.pow_log_le_self k (show Z ≠ 0 by omega)
  have h' : ((k ^ Nat.log k Z : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← Real.log_pow]
  push_cast at h'
  exact Real.log_le_log (pow_pos hk0 _) h'

lemma cPrime_natLog_le {k Z : ℕ} (hZ : 1 ≤ Z) :
    cPrime k * (Nat.log k Z : ℝ) ≤ cPrime k + (if k * k ≤ Z then Real.log Z else 0) := by
  unfold cPrime
  split_ifs with hp hkk
  · have := log_mul_natLog_le hp.two_le hZ
    have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    nlinarith
  · have hlt : Nat.log k Z ≤ 1 := by
      have : Z < k ^ 2 := by rw [sq]; omega
      exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) this)
    have : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    have : (Nat.log k Z : ℝ) ≤ 1 := by exact_mod_cast hlt
    nlinarith
  · simp only [zero_add, zero_mul]
    have : (1 : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hZ
    exact Real.log_nonneg this
  · simp

lemma sum_cPrime_le_theta (M : ℕ) : ∑ k ∈ Ioc 0 M, cPrime k ≤ Chebyshev.theta M := by
  rw [theta_eq_sum_cPrime, Nat.floor_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega
  · intro k _ _; unfold cPrime; split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
    · exact le_refl _

lemma cPrime_nonneg' (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime; split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_refl _

/-- The small-prime range. -/
lemma small_range_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 (n / 10), cPrime k * (-(Lp n k : ℝ)) ≤
      6 * (37 * n) * (Chebyshev.theta (n / 10 : ℕ) + (Real.sqrt (200 * n) + 1) * Real.log (200 * n)) +
        (37 * n) * 100 := by
  have hZ : 1 ≤ 200 * n := by omega
  have hterm : ∀ k ∈ Ioc 0 (n / 10), cPrime k * (-(Lp n k : ℝ)) ≤
      6 * (37 * n) * (cPrime k + (if k * k ≤ 200 * n then Real.log (200 * n : ℕ) else 0)) +
        (37 * n) * (if k ≤ 24 then 4 else 0) := by
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hLp : Lp n k = Lsmall n k := by
      unfold Lp Mcut; rw [if_pos (by omega)]
    rw [hLp]; unfold Lsmall
    simp only [Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat, neg_neg,
      Nat.cast_mul, Nat.cast_ofNat]
    have h1 := cPrime_natLog_le (k := k) hZ
    have hc0 := cPrime_nonneg' k
    have h24 : cPrime k * (padicValNat k 24 : ℝ) ≤ (if k ≤ 24 then 4 else 0) := by
      unfold cPrime
      split_ifs with hp h24
      · have hv : k ^ padicValNat k 24 ∣ 24 := by
          have := Fact.mk hp; exact pow_padicValNat_dvd
        have := Nat.le_of_dvd (by norm_num) hv
        have h' : ((k ^ padicValNat k 24 : ℕ) : ℝ) ≤ 24 := by exact_mod_cast this
        have hk0 : (0 : ℝ) < k := by exact_mod_cast hp.pos
        have : (padicValNat k 24 : ℝ) * Real.log k ≤ Real.log 24 := by
          rw [← Real.log_pow]; push_cast at h'; exact Real.log_le_log (pow_pos hk0 _) h'
        have : Real.log 24 < 4 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 24 / 16 by norm_num)
          have h16 : Real.log 16 = 4 * Real.log 2 := by
            rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
          have := Real.log_two_lt_d9
          have e : Real.log 24 = Real.log (24 / 16) + Real.log 16 := by
            rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
          linarith
        linarith
      · have : padicValNat k 24 = 0 := padicValNat.eq_zero_of_not_dvd (fun h => by
          have := Nat.le_of_dvd (by norm_num) h; omega)
        rw [this]; simp
      · simp
      · simp
    have hn0 : (0 : ℝ) ≤ 37 * n := by positivity
    have e1 := mul_le_mul_of_nonneg_left h1 (show (0 : ℝ) ≤ 6 * (37 * n) by positivity)
    have e2 := mul_le_mul_of_nonneg_left h24 hn0
    push_cast at e1
    nlinarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hθ := sum_cPrime_le_theta (n / 10)
  -- the square-root part
  have hsq : ∑ k ∈ Ioc 0 (n / 10), (if k * k ≤ 200 * n then Real.log (200 * n : ℕ) else 0) ≤
      (Real.sqrt (200 * n) + 1) * Real.log (200 * n) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have hlog : 0 ≤ Real.log (200 * n : ℕ) := Real.log_nonneg (by exact_mod_cast hZ)
    have hcard : (((Ioc 0 (n / 10)).filter fun k => k * k ≤ 200 * n).card : ℝ) ≤
        Real.sqrt (200 * n) + 1 := by
      have hsub : (Ioc 0 (n / 10)).filter (fun k => k * k ≤ 200 * n) ⊆
          Icc 1 (Nat.sqrt (200 * n)) := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
        exact ⟨hk.1.1, Nat.le_sqrt.mpr hk.2⟩
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc] at this
      have h2 : ((Nat.sqrt (200 * n) : ℕ) : ℝ) ≤ Real.sqrt (200 * n) := by
        have := Real.nat_sqrt_le_real_sqrt (a := 200 * n)
        push_cast at this; exact this
      have : (((Ioc 0 (n / 10)).filter fun k => k * k ≤ 200 * n).card : ℝ) ≤
          (Nat.sqrt (200 * n) : ℝ) := by
        exact_mod_cast (show _ ≤ Nat.sqrt (200 * n) by omega)
      linarith
    push_cast at hlog ⊢
    exact mul_le_mul_of_nonneg_right hcard hlog
  have h24 : ∑ k ∈ Ioc 0 (n / 10), (if k ≤ 24 then (4 : ℝ) else 0) ≤ 100 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    have : ((Ioc 0 (n / 10)).filter fun k => k ≤ 24).card ≤ 24 := by
      calc _ ≤ (Icc 1 24).card := Finset.card_le_card (fun k hk => by
            simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢; omega)
        _ = 24 := by simp
    have : (((Ioc 0 (n / 10)).filter fun k => k ≤ 24).card : ℝ) ≤ 24 := by exact_mod_cast this
    linarith
  have hn0 : (0 : ℝ) ≤ 37 * n := by positivity
  push_cast at hsq ⊢
  nlinarith [mul_le_mul_of_nonneg_left h24 hn0,
    mul_le_mul_of_nonneg_left (add_le_add hθ hsq) (show (0 : ℝ) ≤ 6 * (37 * n) by positivity)]

end Apery
end Port0


open Finset in
/-- The platform target `Apery.small_range_le`, restated at top level as `solution`. -/
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Ioc 0 (n / 10), Apery.cPrime k * (-(Apery.Lp n k : ℝ)) ≤
      6 * (37 * n) * (Chebyshev.theta (n / 10 : ℕ) +
          (Real.sqrt (200 * n) + 1) * Real.log (200 * n)) + (37 * n) * 100 :=
  Apery.small_range_le n hn
