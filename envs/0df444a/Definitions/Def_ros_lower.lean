-- Prove2me | Definitions.Def_ros_lower
-- name    : ros_lower
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-10-04T10:47:05.33448+00:00
-- url     : https://prove2.me/theorems/9eb47ff4-0d9a-405c-97aa-dc353028dedf
-- title:
--   Rosser–Schoenfeld Mertens product lower bound: chained kernel certificate infrastructure
-- statement:
--   Certificate infrastructure for the Rosser–Schoenfeld Mertens-product lower bound e^γ log x < ∏_{p≤x} p/(p−1) on 2 ≤ x ≤ 10^8: sieve masks, moment bounds, decimal logarithm certificates, and chained block soundness. Companion of axler_theta_chain_base.
-- source:
--   Rosser & Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94; companion to the platform theorem TaoFivePrimes.rosser_schoenfeld_product_bound_lower; kernel-verified block certificate.

import Definitions.Def_axler_theta_prep

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000000

open Finset Real
namespace RosserLower

open RosserBitSieve RosserBitMoments RosserSieveData RosserProductCertificate RosserScan

def S : ℕ := 10 ^ 15

def logTerm15 (a d i : ℕ) : ℕ :=
  S * 2 * a ^ (2 * i + 1) / ((2 * i + 1) * d ^ (2 * i + 1))

def logSeries15 (a d : ℕ) : ℕ := ((List.range 8).map (logTerm15 a d)).sum

theorem logSeries15_eq (a d : ℕ) :
    logSeries15 a d = ∑ i ∈ Finset.range 8, logTerm15 a d i := by
  rw [logSeries15, ← List.sum_toFinset (logTerm15 a d) (List.nodup_range (n := 8))]
  rfl

def logTermUp15 (a d i : ℕ) : ℕ :=
  (S * 2 * a ^ (2 * i + 1)) ⌈/⌉ ((2 * i + 1) * d ^ (2 * i + 1))

def logSeriesUp15 (a d : ℕ) : ℕ := ((List.range 8).map (logTermUp15 a d)).sum

theorem logSeriesUp15_eq (a d : ℕ) :
    logSeriesUp15 a d = ∑ i ∈ Finset.range 8, logTermUp15 a d i := by
  rw [logSeriesUp15, ← List.sum_toFinset (logTermUp15 a d) (List.nodup_range (n := 8))]
  rfl

def logLo15 (n : ℕ) : ℕ :=
  let k := AxlerTheta.log2k n
  let q := 2 ^ k
  let a := n - q
  let d := n + q
  k * 693147180300000 + logSeries15 a d

def logUp15 (n : ℕ) : ℕ :=
  let k := AxlerTheta.log2k n
  let q := 2 ^ k
  let a := n - q
  let d := n + q
  k * 693147180800001 + logSeriesUp15 a d +
    (S * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2))

theorem logLo15_sound (n : ℕ) (hn : 2 ≤ n) (hbig : n < 2 ^ 64) :
    (logLo15 n : ℝ) ≤ (S : ℝ) * Real.log n := by
  set k := AxlerTheta.log2k n with hk
  set q := 2 ^ k with hq
  have hqle : q ≤ n := by
    rw [hq, hk, AxlerTheta.log2k]
    exact AxlerTheta.pow_log2f_le 64 n hn hbig
  have hqpos : 0 < q := by rw [hq]; positivity
  set a := n - q with ha
  set d := n + q with hd
  have haR : (a : ℝ) = (n : ℝ) - (q : ℝ) := by
    rw [ha]
    exact Nat.cast_sub hqle
  have hdR : (d : ℝ) = (n : ℝ) + (q : ℝ) := by
    rw [hd]
    push_cast
    rfl
  have hdposN : 0 < d := by rw [hd]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  let z : ℝ := ((n : ℝ) - (q : ℝ)) / ((n : ℝ) + (q : ℝ))
  have hz_eq : z = (a : ℝ) / (d : ℝ) := by
    dsimp only [z]
    rw [← haR, ← hdR]
  have hz0 : 0 ≤ z := by
    rw [hz_eq]
    exact div_nonneg (Nat.cast_nonneg a) hdpos.le
  have hz1 : z < 1 := by
    rw [hz_eq, div_lt_one hdpos]
    rw [haR, hdR]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hratio : (1 + z) / (1 - z) = (n : ℝ) / (q : ℝ) := by
    rw [hz_eq, haR, hdR]
    field_simp [hqR.ne']
    ring
  have h := Real.sum_range_le_log_div hz0 hz1 8
  have hlogq : Real.log (q : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [show (q : ℝ) = (2 : ℝ) ^ k from by rw [hq]; push_cast; rfl, Real.log_pow]
  rw [hratio, Real.log_div (by positivity : (n : ℝ) ≠ 0)
    hqR.ne', hlogq] at h
  have hgoal : (logLo15 n : ℝ) =
      ((k * 693147180300000 : ℕ) : ℝ) +
        ∑ i ∈ Finset.range 8,
          ((S * 2 * a ^ (2 * i + 1) / ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) := by
    simp only [logLo15, ← hk, ← hq, ← ha, ← hd]
    rw [logSeries15_eq]
    simp only [logTerm15]
    push_cast
    rfl
  have hK : ((k * 693147180300000 : ℕ) : ℝ) ≤
      (S : ℝ) * ((k : ℝ) * Real.log 2) := by
    have h2 := Real.log_two_gt_d9.le
    calc ((k * 693147180300000 : ℕ) : ℝ)
        = (k : ℝ) * 693147180300000 := by push_cast; ring
      _ = (S : ℝ) * ((k : ℝ) * (0.6931471803 : ℝ)) := by
          rw [show (0.6931471803 : ℝ) = 693147180300000 / 1000000000000000 by norm_num]
          norm_num [S]
          ring
      _ = (S : ℝ) * (k : ℝ) * (0.6931471803 : ℝ) := by ring
      _ ≤ (S : ℝ) * (k : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num [S])
            (Nat.cast_nonneg k))
      _ = (S : ℝ) * ((k : ℝ) * Real.log 2) := by ring
  have hterm : ∀ i, ((S * 2 * a ^ (2 * i + 1) /
        ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) ≤
      (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
    intro i
    calc ((S * 2 * a ^ (2 * i + 1) /
          ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)
        ≤ ((S * 2 * a ^ (2 * i + 1) : ℕ) : ℝ) /
            (((2 * i + 1) * d ^ (2 * i + 1) : ℕ) : ℝ) := AxlerTheta.cast_div_le_real
      _ = ((S : ℝ) * 2 * (a : ℝ) ^ (2 * i + 1)) /
            (((2 * i + 1) : ℝ) * (d : ℝ) ^ (2 * i + 1)) := by push_cast; ring
      _ = (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
          have h2i1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', h2i1]
  have hsum : (∑ i ∈ Finset.range 8,
        ((S * 2 * a ^ (2 * i + 1) /
          ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) ≤
      (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) := by
    calc (∑ i ∈ Finset.range 8, ((S * 2 * a ^ (2 * i + 1) /
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ))
        ≤ ∑ i ∈ Finset.range 8,
            (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (S : ℝ) * 2 * (∑ i ∈ Finset.range 8,
            z ^ (2 * i + 1) / (2 * i + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) := by
          have h2 : (2 : ℝ) * (∑ i ∈ Finset.range 8,
              z ^ (2 * i + 1) / (2 * i + 1)) ≤
              Real.log n - (k : ℝ) * Real.log 2 := by linarith only [h]
          calc (S : ℝ) * 2 * (∑ i ∈ Finset.range 8,
                z ^ (2 * i + 1) / (2 * i + 1))
              = (S : ℝ) * (2 * (∑ i ∈ Finset.range 8,
                z ^ (2 * i + 1) / (2 * i + 1))) := by ring
            _ ≤ (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) :=
                mul_le_mul_of_nonneg_left h2 (by norm_num [S])
  rw [hgoal]
  have hfinal : (S : ℝ) * ((k : ℝ) * Real.log 2) +
      (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) =
      (S : ℝ) * Real.log n := by ring
  linarith only [hK, hsum, hfinal]

theorem logUp15_sound (n : ℕ) (hn : 2 ≤ n) (hbig : n < 2 ^ 64) :
    (S : ℝ) * Real.log n ≤ (logUp15 n : ℝ) := by
  set k := AxlerTheta.log2k n with hk
  set q := 2 ^ k with hq
  have hqle : q ≤ n := by
    rw [hq, hk, AxlerTheta.log2k]
    exact AxlerTheta.pow_log2f_le 64 n hn hbig
  have hqpos : 0 < q := by rw [hq]; positivity
  set a := n - q with ha
  set d := n + q with hd
  have haR : (a : ℝ) = (n : ℝ) - (q : ℝ) := by
    rw [ha]
    exact Nat.cast_sub hqle
  have hdR : (d : ℝ) = (n : ℝ) + (q : ℝ) := by
    rw [hd]
    push_cast
    rfl
  have hda : a < d := by rw [ha, hd]; omega
  have hd2a2 : 0 < d ^ 2 - a ^ 2 := by
    have h : a ^ 2 < d ^ 2 := Nat.pow_lt_pow_left hda (by norm_num)
    omega
  have hdposN : 0 < d := by rw [hd]; omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hdposN
  let z : ℝ := ((n : ℝ) - (q : ℝ)) / ((n : ℝ) + (q : ℝ))
  have hz_eq : z = (a : ℝ) / (d : ℝ) := by
    dsimp only [z]
    rw [← haR, ← hdR]
  have hz0 : 0 ≤ z := by
    rw [hz_eq]
    exact div_nonneg (Nat.cast_nonneg a) hdpos.le
  have hz1 : z < 1 := by
    rw [hz_eq, div_lt_one hdpos]
    rw [haR, hdR]
    have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
    linarith
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hratio : (1 + z) / (1 - z) = (n : ℝ) / (q : ℝ) := by
    rw [hz_eq, haR, hdR]
    field_simp [hqR.ne']
    ring
  have h := Real.log_div_le_sum_range_add hz0 hz1 8
  have hlogq : Real.log (q : ℝ) = (k : ℝ) * Real.log 2 := by
    rw [show (q : ℝ) = (2 : ℝ) ^ k from by rw [hq]; push_cast; rfl, Real.log_pow]
  rw [hratio, Real.log_div (by positivity : (n : ℝ) ≠ 0)
    hqR.ne', hlogq] at h
  have hgoal : (logUp15 n : ℝ) =
      ((k * 693147180800001 : ℕ) : ℝ) +
        (∑ i ∈ Finset.range 8,
          (((S * 2 * a ^ (2 * i + 1)) ⌈/⌉
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) +
        (((S * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
    simp only [logUp15, ← hk, ← hq, ← ha, ← hd]
    rw [logSeriesUp15_eq]
    simp only [logTermUp15]
    push_cast
    rfl
  have hK : (S : ℝ) * ((k : ℝ) * Real.log 2) ≤
      ((k * 693147180800001 : ℕ) : ℝ) := by
    have h2 := Real.log_two_lt_d9.le
    calc (S : ℝ) * ((k : ℝ) * Real.log 2)
        ≤ (S : ℝ) * ((k : ℝ) * (0.6931471808 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num [S])
          exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
      _ = (k : ℝ) * 693147180800000 := by
          rw [show (0.6931471808 : ℝ) = 6931471808 / 10000000000 by norm_num]
          norm_num [S]
          ring
      _ ≤ (k : ℝ) * 693147180800001 := by
          have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith
      _ = ((k * 693147180800001 : ℕ) : ℝ) := by push_cast; ring
  have hterm : ∀ i, (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) ≤
      (((S * 2 * a ^ (2 * i + 1)) ⌈/⌉
        ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) := by
    intro i
    calc (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))
        = ((S : ℝ) * 2 * (a : ℝ) ^ (2 * i + 1)) /
            (((2 * i + 1) : ℝ) * (d : ℝ) ^ (2 * i + 1)) := by
          have h2i1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', h2i1]
      _ = ((S * 2 * a ^ (2 * i + 1) : ℕ) : ℝ) /
            (((2 * i + 1) * d ^ (2 * i + 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((S * 2 * a ^ (2 * i + 1)) ⌈/⌉
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) :=
          AxlerTheta.real_div_le_cast_ceilDiv (by positivity)
  have htail : (S : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2))) ≤
      (((S * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
    have hd2a2R : (0 : ℝ) < (d : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
      have hle : a ^ 2 ≤ d ^ 2 := le_of_lt (by omega : a ^ 2 < d ^ 2)
      rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub hle]
      exact_mod_cast hd2a2
    calc (S : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2)))
        = (S : ℝ) * 2 * (a : ℝ) ^ 17 /
            ((d : ℝ) ^ 15 * ((d : ℝ) ^ 2 - (a : ℝ) ^ 2)) := by
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', hd2a2R.ne']
      _ ≤ (((S * 2 * a ^ 17) ⌈/⌉
            (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
          have hle : a ^ 2 ≤ d ^ 2 := by omega
          have h := AxlerTheta.real_div_le_cast_ceilDiv (x := S * 2 * a ^ 17)
            (m := d ^ 15 * (d ^ 2 - a ^ 2)) (by positivity)
          push_cast [Nat.cast_sub hle] at h
          exact h
  have hsplit : (S : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
        z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) =
      (∑ i ∈ Finset.range 8,
        (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))) +
      (S : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2))) := by
    rw [show (S : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
          z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) =
        (S : ℝ) * 2 * (∑ i ∈ Finset.range 8,
          z ^ (2 * i + 1) / (2 * i + 1)) +
        (S : ℝ) * 2 * (z ^ 17 / (1 - z ^ 2)) from by ring]
    rw [Finset.mul_sum]
    ring
  have h2 : (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) ≤
      (S : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
        z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) := by
    have h' : (1 : ℝ) / 2 * (Real.log n - (k : ℝ) * Real.log 2) ≤
        (∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) +
          z ^ 17 / (1 - z ^ 2) := h
    have h2' : Real.log n - (k : ℝ) * Real.log 2 ≤
        2 * ((∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) +
          z ^ 17 / (1 - z ^ 2)) := by linarith only [h']
    have hs0 : (0 : ℝ) ≤ (S : ℝ) := by norm_num [S]
    exact mul_le_mul_of_nonneg_left h2' hs0
  rw [hgoal]
  have hbound :
      (S : ℝ) * ((k : ℝ) * Real.log 2) +
          (∑ i ∈ Finset.range 8, (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))) +
          ((S : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2)))) ≤
      (((k * 693147180800001 : ℕ) : ℝ) +
          (∑ i ∈ Finset.range 8,
            (((S * 2 * a ^ (2 * i + 1)) ⌈/⌉
              ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) +
          (((S * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ)) := by
    exact add_le_add
      (add_le_add hK (Finset.sum_le_sum (fun i _ => hterm i)))
      htail
  rw [hsplit] at h2
  have hfinal : (S : ℝ) * ((k : ℝ) * Real.log 2) +
      (S : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) =
      (S : ℝ) * Real.log n := by ring
  linarith only [h2, hbound, hfinal]

/-- Upper bound: `S * log (log b) ≤ llUp b` (when the sub is exact). -/
theorem llUp_sound (b : ℕ) (h2 : 2 ≤ b) (hb8 : b ≤ 10 ^ 8)
    (hlo2 : 2 ≤ logUp15 b) (hlo64 : logUp15 b < 2 ^ 64)
    (hsub : logLo15 S ≤ logUp15 (logUp15 b)) :
    (S : ℝ) * Real.log (Real.log b) ≤
      ((logUp15 (logUp15 b) - logLo15 S : ℕ) : ℝ) := by
  have hb64 : b < 2 ^ 64 := by omega
  have hS2 : 2 ≤ S := by norm_num [S]
  have hS64 : S < 2 ^ 64 := by norm_num [S]
  have hSpos : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hlo : (logLo15 S : ℝ) ≤ (S : ℝ) * Real.log S := logLo15_sound S hS2 hS64
  have hhi : (S : ℝ) * Real.log b ≤ (logUp15 b : ℝ) := logUp15_sound b h2 hb64
  have hhi_hi : (S : ℝ) * Real.log (logUp15 b : ℝ) ≤
      (logUp15 (logUp15 b) : ℝ) := logUp15_sound (logUp15 b) hlo2 hlo64
  have hcast : ((logUp15 (logUp15 b) - logLo15 S : ℕ) : ℝ) =
      (logUp15 (logUp15 b) : ℝ) - (logLo15 S : ℝ) := Nat.cast_sub hsub
  have hlogb : (0 : ℝ) < Real.log b := Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hdiv : Real.log b ≤ (logUp15 b : ℝ) / (S : ℝ) := by
    rw [le_div_iff₀ hSpos]
    linarith [hhi]
  have hlogdiv : Real.log (Real.log b) ≤ Real.log ((logUp15 b : ℝ) / (S : ℝ)) :=
    Real.log_le_log hlogb hdiv
  have hsplit : Real.log ((logUp15 b : ℝ) / (S : ℝ)) =
      Real.log (logUp15 b : ℝ) - Real.log S := by
    apply Real.log_div
    · have : (2 : ℝ) ≤ (logUp15 b : ℝ) := by exact_mod_cast hlo2
      linarith
    · exact hSpos.ne'
  rw [hsplit] at hlogdiv
  rw [hcast]
  have hmain : (S : ℝ) * Real.log (Real.log b) ≤
      (logUp15 (logUp15 b) : ℝ) - (logLo15 S : ℝ) := by
    have hmul : (S : ℝ) * Real.log (Real.log b) ≤
        (S : ℝ) * (Real.log (logUp15 b : ℝ) - Real.log S) :=
      mul_le_mul_of_nonneg_left hlogdiv hSpos.le
    have hdist : (S : ℝ) * (Real.log (logUp15 b : ℝ) - Real.log S) =
        (S : ℝ) * Real.log (logUp15 b : ℝ) - (S : ℝ) * Real.log S := by ring
    rw [hdist] at hmul
    linarith [hhi_hi, hlo]
  exact hmain

-- ============================================================
-- Part B: prime product bridge, moments exactness, increment bound
-- ============================================================

noncomputable def logProd (n : ℕ) : ℝ := Real.log (eulerProduct n)

theorem eulerProduct_pos (n : ℕ) : 0 < eulerProduct n := by
  unfold eulerProduct
  apply Finset.prod_pos
  intro p hp
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
  exact div_pos (by linarith) (by linarith)

theorem eulerProduct_sdiff (a b : ℕ) (hab : a ≤ b) :
    eulerProduct b / eulerProduct a =
      ∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (p : ℝ) / ((p : ℝ) - 1) := by
  have hne := (eulerProduct_pos a).ne'
  unfold eulerProduct
  rw [← Finset.prod_sdiff (s₁ := Nat.primesLE a) (s₂ := Nat.primesLE b)
    (Nat.primesLE_mono hab) (f := fun p : ℕ => (p : ℝ) / ((p : ℝ) - 1))]
  exact mul_div_cancel_right₀ _ hne

theorem logProd_mono (a b : ℕ) (hab : a ≤ b) : logProd a ≤ logProd b := by
  apply Real.log_le_log (eulerProduct_pos a)
  exact eulerProduct_mono hab

theorem sum_log_sdiff (a b : ℕ) (hab : a ≤ b) :
    logProd b - logProd a =
      ∑ p ∈ Nat.primesLE b \ Nat.primesLE a,
        Real.log (1 + 1 / ((p : ℝ) - 1)) := by
  have hb := eulerProduct_pos b
  have ha := eulerProduct_pos a
  have h1 : logProd b - logProd a =
      Real.log (∏ p ∈ Nat.primesLE b \ Nat.primesLE a, (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [logProd, logProd, ← Real.log_div hb.ne' ha.ne', eulerProduct_sdiff a b hab]
  rw [h1, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.two_le
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    rw [show (p : ℝ) / ((p : ℝ) - 1) = 1 + 1 / ((p : ℝ) - 1) from by
      field_simp; ring]
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2.two_le
    exact ne_of_gt (div_pos (by linarith) (by linarith))

theorem filter_range_pad_aux (w len k : ℕ)
    (h : ∀ i, w.testBit i = true → i < len) :
    (List.range (len + k)).filter (fun i => w.testBit i) =
      (List.range len).filter (fun i => w.testBit i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show len + (k + 1) = (len + k) + 1 by omega, List.range_succ, List.filter_append, ih]
    have hf : w.testBit (len + k) = false := by
      cases hb : w.testBit (len + k) with
      | false => rfl
      | true => exact absurd (h _ hb) (by omega)
    simp [hf]

theorem filter_range_pad (w len N : ℕ) (hw : w < 2 ^ len) (hle : len ≤ N) :
    (List.range N).filter (fun i => w.testBit i) =
      (List.range len).filter (fun i => w.testBit i) := by
  have hlt : ∀ i, w.testBit i = true → i < len := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    have hw' : w < 2 ^ i := lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) hcon)
    rw [Nat.testBit_eq_false_of_lt hw'] at hi
    exact Bool.noConfusion hi
  have := filter_range_pad_aux w len (N - len) hlt
  rwa [show len + (N - len) = N by omega] at this

theorem windowMoments_prime_offsets (base top a b : ℕ)
    (hbase : base ≤ a) (hb1 : 1 ≤ base) (hsq : top ≤ base * base)
    (hab : a < b) (hbtop : b ≤ top) (h8 : b ≤ 10 ^ 8) (hlen : b - a ≤ 2 ^ 13) :
    windowMoments (RosserSieveData.mask base top) (a - base) (b - a) =
      moments (((List.range (b - a)).filter
        (fun i => decide (Nat.Prime (a + 1 + i)))).map (fun i => i + 1)) := by
  set m := RosserSieveData.mask base top with hm
  set w := m / 2 ^ (a - base) % 2 ^ (b - a) with hw
  have hwlt : w < 2 ^ (b - a) := by
    rw [hw]
    exact Nat.mod_lt _ (Nat.pow_pos (by norm_num))
  have hbit : ∀ i, i < b - a → w.testBit i = decide (Nat.Prime (a + 1 + i)) := by
    intro i hi
    have hs : w.testBit i = m.testBit (a - base + i) := by
      rw [hw]
      exact AxlerSieve.slice_bit (base := base) (a := a) (b := b) (m := m) hi
    rw [hs]
    by_cases hp : Nat.Prime (a + 1 + i)
    · rw [decide_eq_true hp]
      exact (AxlerSieve.mask_bit_iff (base := base) (top := top) (a := a) (i := i)
        hbase hb1 hsq (by omega) (by omega)).mpr hp
    · rw [decide_eq_false hp]
      apply Bool.eq_false_iff.mpr
      intro hb2
      exact hp ((AxlerSieve.mask_bit_iff (base := base) (top := top) (a := a) (i := i)
        hbase hb1 hsq (by omega) (by omega)).mp hb2)
  rw [windowMoments_sound]
  rw [show windowOffsets 13 m (a - base) (b - a) =
      (enumBits 13 0 w).map (fun d => d + 1) from by
    simp only [RosserBitSieve.windowOffsets]
    rw [← hw]]
  apply moments_perm
  apply List.Perm.map
  refine (RosserPackedMoments.enumBits_perm_filter 13 w).trans ?_
  rw [filter_range_pad w (b - a) (2 ^ 13) hwlt hlen]
  exact List.Perm.of_eq (List.filter_congr (fun i hi => hbit i (List.mem_range.mp hi)))

theorem log_one_add_ge (a b p : ℕ) (ha : 2 ≤ a) (hap : a < p) (hpb : p ≤ b) :
    1 / ((a : ℝ) - 1 / 2) - ((p : ℝ) - (a : ℝ)) / ((a : ℝ) - 1 / 2) ^ 2
      + ((p : ℝ) - (a : ℝ)) ^ 2 / (((a : ℝ) - 1 / 2) ^ 2 * ((b : ℝ) - 1 / 2))
    ≤ Real.log (1 + 1 / ((p : ℝ) - 1)) := by
  have hp2 : 2 ≤ p := by omega
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  set x0 : ℝ := (a : ℝ) - 1 / 2 with hx0
  set y : ℝ := (p : ℝ) - 1 / 2 with hy
  set Y : ℝ := (b : ℝ) - 1 / 2 with hY
  have hx0pos : 0 < x0 := by
    rw [hx0]
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hypos : 0 < y := by
    rw [hy]
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hYpos : 0 < Y := by
    rw [hY]
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
    linarith
  have hyY : y ≤ Y := by
    rw [hy, hY]
    exact sub_le_sub_right (by exact_mod_cast hpb) (1 / 2)
  have hxy : (p : ℝ) - (a : ℝ) = y - x0 := by
    rw [hy, hx0]
    ring
  rw [hxy]
  have hx : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
  have hpade := Real.le_log_one_add_of_nonneg hx
  have hp_eq : 2 * (1 / ((p : ℝ) - 1)) / ((1 / ((p : ℝ) - 1)) + 2) = 1 / y := by
    rw [hy]
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 1 / 2 ≠ 0 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
      linarith
    have h3 : 2 * (p : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (show 1 < p by omega)
      linarith
    field_simp [h1, h2, h3]
    ring
  have hid : 1 / y = 1 / x0 - (y - x0) / x0 ^ 2 + (y - x0) ^ 2 / (x0 ^ 2 * y) := by
    field_simp [hx0pos.ne', hypos.ne']
    ring
  have hlast : (y - x0) ^ 2 / (x0 ^ 2 * Y) ≤ (y - x0) ^ 2 / (x0 ^ 2 * y) := by
    have hd2 : x0 ^ 2 * y ≤ x0 ^ 2 * Y := by nlinarith
    have hone : 1 / (x0 ^ 2 * Y) ≤ 1 / (x0 ^ 2 * y) :=
      one_div_le_one_div_of_le (by positivity) hd2
    have hone' : (x0 ^ 2 * Y)⁻¹ ≤ (x0 ^ 2 * y)⁻¹ := by
      simpa only [one_div] using hone
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hone' (sq_nonneg _)
  calc 1 / x0 - (y - x0) / x0 ^ 2 + (y - x0) ^ 2 / (x0 ^ 2 * Y)
      ≤ 1 / x0 - (y - x0) / x0 ^ 2 + (y - x0) ^ 2 / (x0 ^ 2 * y) := by
        linarith only [hlast]
    _ = 1 / y := hid.symm
    _ = 2 * (1 / ((p : ℝ) - 1)) / ((1 / ((p : ℝ) - 1)) + 2) := hp_eq.symm
    _ ≤ Real.log (1 + 1 / ((p : ℝ) - 1)) := hpade

def blockNum (s : Moments) (a b : ℕ) : ℕ :=
  S * ((2 * s.count * (2 * a - 1) * (2 * b - 1) + 8 * s.second) -
        4 * s.first * (2 * b - 1)) /
    ((2 * a - 1) * (2 * a - 1) * (2 * b - 1))

def incrOf (s : Moments) (a b : ℕ) : ℕ :=
  if s.count = 1 then logSeries15 1 (2 * (a + s.first) - 1)
  else blockNum s a b

def gammaUpS : ℕ := 577216170667183

structure Blk where
  a : ℕ
  b : ℕ
  L : ℕ
  L' : ℕ
  deriving DecidableEq, Repr

structure Grp where
  lo : ℕ
  base : ℕ
  top : ℕ
  lin : ℕ
  lfin : ℕ
  blks : List Blk
  deriving Repr

theorem slice_eq (m shift len : ℕ) :
    (m >>> shift) &&& (2 ^ len - 1) = m / 2 ^ shift % 2 ^ len := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

def blkOK (gbase m : ℕ) (B : Blk) (L : ℕ) : Bool × ℕ :=
  if B.b = 0 then (false, L)
  else
    forceNat ((m >>> (B.a - gbase)) &&& (2 ^ (B.b - B.a) - 1)) fun w =>
    forceNat (logUp15 B.b) fun lhi =>
    forceNat (logUp15 lhi) fun hhi =>
    let ok := decide (2 ≤ lhi ∧ lhi < 2 ^ 64 ∧ logLo15 S ≤ hhi ∧
      gammaUpS + (hhi - logLo15 S) < L)
    forceNat (L + incrOf (fastMoments 10 1 w) B.a B.b) fun L' => (ok, L')

def grpGo (G : Grp) (gbase m : ℕ) : ℕ → ℕ → List Blk → Bool
  | prev, L, [] => (prev = G.top) && (L = G.lfin)
  | prev, L, B :: rest =>
    match blkOK gbase m B L with
    | (ok, L') => (prev = B.a) && ok && grpGo G gbase m B.b L' rest

def grpOK (G : Grp) : Bool :=
  forceNat (mask G.base G.top) fun m => grpGo G G.base m G.base G.lin G.blks

def grpWF (G : Grp) : Bool :=
  decide (3 ≤ G.lo ∧ (G.base = G.lo ∨ (Nat.Prime G.lo ∧ G.base = G.lo + 1)) ∧
    G.base < G.top ∧ G.top ≤ G.base * G.base ∧ G.top ≤ 10 ^ 8) &&
  G.blks.all (fun B => decide (G.base ≤ B.a ∧ B.a < B.b ∧ B.b ≤ G.top ∧
    B.b - B.a ≤ 2 ^ 13 ∧ B.b ≤ 10 ^ 8))

def blkSpec (gbase m : ℕ) (B : Blk) (L L' : ℕ) : Prop :=
  L' = L + incrOf (windowMoments m (B.a - gbase) (B.b - B.a)) B.a B.b ∧
  ∃ lhi hhi : ℕ, lhi = logUp15 B.b ∧ hhi = logUp15 lhi ∧
    2 ≤ lhi ∧ lhi < 2 ^ 64 ∧ logLo15 S ≤ hhi ∧
    gammaUpS + (hhi - logLo15 S) < L

theorem blkOK_spec {gbase m : ℕ} {B : Blk} {L L' : ℕ}
    (h : blkOK gbase m B L = (true, L')) :
    blkSpec gbase m B L L' := by
  unfold blkOK blkSpec at *
  by_cases hz : B.b = 0
  · rw [if_pos hz] at h
    simp at h
  rw [if_neg hz] at h
  simp only [forceNat_eq] at h ⊢
  have hfst : decide (2 ≤ logUp15 B.b ∧ logUp15 B.b < 2 ^ 64 ∧
      logLo15 S ≤ logUp15 (logUp15 B.b) ∧
      gammaUpS + (logUp15 (logUp15 B.b) - logLo15 S) < L) = true :=
    congrArg Prod.fst h
  have hsnd : L + incrOf (windowMoments m (B.a - gbase) (B.b - B.a)) B.a B.b = L' := by
    simpa only [slice_eq, windowMoments] using congrArg Prod.snd h
  obtain ⟨h1, h2, h3, h4⟩ := of_decide_eq_true hfst
  exact ⟨hsnd.symm, _, _, rfl, rfl, h1, h2, h3, h4⟩

def grpSpec (G : Grp) (gbase m : ℕ) : ℕ → ℕ → List Blk → Prop
  | prev, L, [] => prev = G.top ∧ L = G.lfin
  | prev, L, B :: rest =>
    prev = B.a ∧ ∃ L', blkSpec gbase m B L L' ∧ grpSpec G gbase m B.b L' rest

theorem blkOK_spec' {gbase m : ℕ} {B : Blk} {L L' : ℕ} {ok : Bool}
    (h : blkOK gbase m B L = (ok, L')) (hok : ok = true) :
    blkSpec gbase m B L L' :=
  blkOK_spec (by rw [hok] at h; exact h)

theorem grpGo_spec (G : Grp) (gbase m : ℕ) :
    ∀ (prev L : ℕ) (blks : List Blk),
      grpGo G gbase m prev L blks = true → grpSpec G gbase m prev L blks := by
  intro prev L blks
  induction blks generalizing prev L with
  | nil =>
    intro h
    simp only [grpGo, grpSpec] at h ⊢
    simpa [and_assoc] using h
  | cons B rest ih =>
    intro h
    simp only [grpGo] at h
    cases hb : blkOK gbase m B L with
    | mk ok L' =>
      rw [hb] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hprev, hok⟩, hrest⟩ := h
      exact ⟨hprev, L', blkOK_spec' hb hok, ih B.b L' hrest⟩

theorem grpOK_spec {G : Grp} (h : grpOK G = true) :
    grpSpec G G.base (mask G.base G.top) G.base G.lin G.blks := by
  unfold grpOK at h
  simp only [forceNat_eq] at h
  exact grpGo_spec G G.base (mask G.base G.top) G.base G.lin G.blks h

theorem grpWF_spec {G : Grp} (h : grpWF G = true) :
    3 ≤ G.lo ∧ (G.base = G.lo ∨ (Nat.Prime G.lo ∧ G.base = G.lo + 1)) ∧
      G.base < G.top ∧ G.top ≤ G.base * G.base ∧ G.top ≤ 10 ^ 8 ∧
      ∀ B ∈ G.blks, G.base ≤ B.a ∧ B.a < B.b ∧ B.b ≤ G.top ∧
        B.b - B.a ≤ 2 ^ 13 ∧ B.b ≤ 10 ^ 8 := by
  rw [grpWF, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have h1' := of_decide_eq_true h1
  refine ⟨h1'.1, h1'.2.1, h1'.2.2.1, h1'.2.2.2.1, h1'.2.2.2.2, ?_⟩
  exact fun B hB => of_decide_eq_true (List.all_eq_true.mp h2 B hB)

theorem cast_sum_eq (ds : List ℕ) :
    ((ds.sum : ℕ) : ℝ) = (ds.map (fun d : ℕ => (d : ℝ))).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp only [List.sum_cons, List.map_cons, List.sum_cons, Nat.cast_add, ih]

theorem cast_sum_sq_eq (ds : List ℕ) :
    (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) =
      (ds.map (fun d : ℕ => (d : ℝ) ^ 2)).sum := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_pow, ih]

theorem blockNum_le_log (a b : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hab : a < b)
    (hds : ds.Nodup) (hpos : ∀ d ∈ ds, 1 ≤ d) (hle : ∀ d ∈ ds, d ≤ b - a)
    (hprime : ∀ d ∈ ds, Nat.Prime (a + d))
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds) :
    (blockNum (moments ds) a b : ℝ) ≤ (S : ℝ) * (logProd b - logProd a) := by
  have hb : a ≤ b := le_of_lt hab
  set ps := ds.map (fun d => a + d) with hpsdef
  have hinj : Function.Injective (fun d : ℕ => a + d) := by
    intro x y h
    change a + x = a + y at h
    omega
  have hps : ps.Nodup := by
    rw [hpsdef]
    exact List.Nodup.map hinj hds
  have hpsset : ps.toFinset = Nat.primesLE b \ Nat.primesLE a := by
    apply Finset.Subset.antisymm
    · intro p hp
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      rw [Finset.mem_sdiff]
      constructor
      · exact Nat.mem_primesLE.mpr ⟨by have := hle d hd; omega, hprime d hd⟩
      · intro hpa
        have hple : a + d ≤ a := (Nat.mem_primesLE.mp hpa).1
        have := hpos d hd
        omega
    · intro p hp
      obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
      obtain ⟨hpb', hpp⟩ := Nat.mem_primesLE.mp hpb
      have hap : a < p := by
        by_contra h
        exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpp⟩)
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨p - a, hcover p hpp hap hpb', by omega⟩
  have hlogsum : logProd b - logProd a =
      ds.toFinset.sum (fun d : ℕ => Real.log (1 + 1 / ((a : ℝ) + d - 1))) := by
    rw [sum_log_sdiff a b hb, ← hpsset, List.sum_toFinset _ hps, hpsdef, List.map_map]
    rw [List.sum_toFinset (l := ds)
      (fun d : ℕ => Real.log (1 + 1 / ((a : ℝ) + d - 1))) hds]
    congr 1
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp_def]
    have e : ((a + d : ℕ) : ℝ) - 1 = (a : ℝ) + d - 1 := by push_cast; ring
    rw [e]
  set x0 : ℝ := (a : ℝ) - 1 / 2 with hx0
  set Y : ℝ := (b : ℝ) - 1 / 2 with hY
  have hx0pos : 0 < x0 := by
    rw [hx0]
    have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    linarith
  have hYpos : 0 < Y := by
    rw [hY]
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast (show 1 ≤ b by omega)
    linarith
  set Lsum := ds.toFinset.sum
    (fun d => 1 / x0 - (d : ℝ) / x0 ^ 2 + (d : ℝ) ^ 2 / (x0 ^ 2 * Y)) with hLsum
  have hlow : Lsum = (ds.toFinset.card : ℝ) / x0 -
      (ds.toFinset.sum (fun d : ℕ => (d : ℝ))) / x0 ^ 2 +
      (ds.toFinset.sum (fun d : ℕ => (d : ℝ) ^ 2)) / (x0 ^ 2 * Y) := by
    rw [hLsum]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_div (s := ds.toFinset) (f := fun d : ℕ => (d : ℝ)) (a := x0 ^ 2)]
    rw [← Finset.sum_div (s := ds.toFinset) (f := fun d : ℕ => (d : ℝ) ^ 2)
      (a := x0 ^ 2 * Y)]
    ring
  have hu : (ds.sum : ℝ) = ds.toFinset.sum (fun d : ℕ => (d : ℝ)) := by
    rw [cast_sum_eq ds, ← List.sum_toFinset (fun d : ℕ => (d : ℝ)) hds]
  have hv : (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) =
      ds.toFinset.sum (fun d : ℕ => (d : ℝ) ^ 2) := by
    rw [cast_sum_sq_eq ds, ← List.sum_toFinset (fun d : ℕ => (d : ℝ) ^ 2) hds]
  have hn : (ds.length : ℝ) = (ds.toFinset.card : ℝ) := by
    rw [List.toFinset_card_of_nodup hds]
  have hterm : ∀ d ∈ ds.toFinset,
      1 / x0 - (d : ℝ) / x0 ^ 2 + (d : ℝ) ^ 2 / (x0 ^ 2 * Y) ≤
        Real.log (1 + 1 / ((a : ℝ) + d - 1)) := by
    intro d hd
    have hd' := List.mem_toFinset.mp hd
    have h1 := hpos d hd'
    have h2 := hle d hd'
    have hinst := log_one_add_ge a b (a + d) ha (by omega) (by omega)
    have e1 : ((a + d : ℕ) : ℝ) - (a : ℝ) = (d : ℝ) := by push_cast; ring
    have e2 : ((a + d : ℕ) : ℝ) - 1 = (a : ℝ) + d - 1 := by push_cast; ring
    rw [e1, e2] at hinst
    exact hinst
  by_cases hcase : 4 * ds.sum * (2 * b - 1) ≤
    2 * ds.length * (2 * a - 1) * (2 * b - 1) + 8 * (ds.map (fun d => d ^ 2)).sum
  · have hA : ((2 * a - 1 : ℕ) : ℝ) = 2 * (a : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * a)]; push_cast; ring
    have hB : ((2 * b - 1 : ℕ) : ℝ) = 2 * (b : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * b)]; push_cast; ring
    have hA0 : 2 * (a : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      linarith
    have hB0 : 2 * (b : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (b : ℝ) := by
        exact_mod_cast (show 2 ≤ b by omega)
      linarith
    have hsum : (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) =
        ds.toFinset.sum (fun d : ℕ => (d : ℝ) ^ 2) := hv
    have hnum : (blockNum (moments ds) a b : ℝ) ≤ (S : ℝ) * Lsum := by
      calc (blockNum (moments ds) a b : ℝ)
          ≤ ((S * ((2 * ds.length * (2 * a - 1) * (2 * b - 1) +
                8 * (ds.map (fun d => d ^ 2)).sum) -
              4 * ds.sum * (2 * b - 1)) : ℕ) : ℝ) /
              (((2 * a - 1) * (2 * a - 1) * (2 * b - 1) : ℕ) : ℝ) :=
            Nat.cast_div_le
        _ = (S : ℝ) * ((2 * (ds.length : ℝ) * (2 * (a : ℝ) - 1) * (2 * (b : ℝ) - 1) +
                8 * (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) -
                4 * (ds.sum : ℝ) * (2 * (b : ℝ) - 1)) /
              ((2 * (a : ℝ) - 1) * (2 * (a : ℝ) - 1) * (2 * (b : ℝ) - 1))) := by
            simp only [Nat.cast_mul]
            rw [Nat.cast_sub hcase]
            simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, hA, hB]
            ring
        _ = (S : ℝ) * Lsum := by
            have halg : (2 * (ds.length : ℝ) * (2 * (a : ℝ) - 1) * (2 * (b : ℝ) - 1) +
                    8 * (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) -
                    4 * (ds.sum : ℝ) * (2 * (b : ℝ) - 1)) /
                  ((2 * (a : ℝ) - 1) * (2 * (a : ℝ) - 1) * (2 * (b : ℝ) - 1)) =
                  (ds.length : ℝ) / ((a : ℝ) - 1 / 2) -
                    (ds.sum : ℝ) / ((a : ℝ) - 1 / 2) ^ 2 +
                    (((ds.map (fun d => d ^ 2)).sum : ℕ) : ℝ) /
                      (((a : ℝ) - 1 / 2) ^ 2 * ((b : ℝ) - 1 / 2)) := by
              have hx : (a : ℝ) - 1 / 2 ≠ 0 := by
                have : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
                linarith
              have hy : (b : ℝ) - 1 / 2 ≠ 0 := by
                have : (2 : ℝ) ≤ (b : ℝ) := by
                  exact_mod_cast (show 2 ≤ b by omega)
                linarith
              field_simp
              ring
            rw [halg, hlow, hu, hsum, hn, hx0, hY]
    calc (blockNum (moments ds) a b : ℝ)
        ≤ (S : ℝ) * Lsum := hnum
      _ ≤ (S : ℝ) * (logProd b - logProd a) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num [S])
          rw [hlogsum, hLsum]
          exact Finset.sum_le_sum hterm
  · have hz : blockNum (moments ds) a b = 0 := by
      simp only [blockNum, moments]
      rw [Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hcase))]
      simp
    rw [hz, Nat.cast_zero]
    exact mul_nonneg (by norm_num [S]) (sub_nonneg.mpr (logProd_mono a b hb))

theorem logSeries15_one_le_step (r : ℕ) (hr : 2 ≤ r) :
    (logSeries15 1 (2 * r - 1) : ℝ) ≤
      (S : ℝ) * (Real.log r - Real.log (r - 1)) := by
  set dd : ℕ := 2 * r - 1 with hdd
  have hdd3 : 3 ≤ dd := by omega
  have hdposN : 0 < dd := by omega
  have hdpos : (0 : ℝ) < (dd : ℝ) := by exact_mod_cast hdposN
  let z : ℝ := 1 / (dd : ℝ)
  have hz_eq : z = (1 : ℝ) / (dd : ℝ) := rfl
  have hz0 : 0 ≤ z := by rw [hz_eq]; positivity
  have hz1 : z < 1 := by
    rw [hz_eq, div_lt_one hdpos]
    exact_mod_cast (show 1 < dd by omega)
  have hdR : (dd : ℝ) = 2 * (r : ℝ) - 1 := by
    rw [hdd, Nat.cast_sub (by omega : 1 ≤ 2 * r)]
    push_cast
    ring
  have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1pos : (0 : ℝ) < (r : ℝ) - 1 := by linarith
  have hratio : (1 + z) / (1 - z) = (r : ℝ) / ((r : ℝ) - 1) := by
    have hd1 : (2 * (r : ℝ) - 1) ≠ 0 := by linarith
    have hr1 : (r : ℝ) - 1 ≠ 0 := by linarith
    have hden : (1 : ℝ) - 1 / (2 * (r : ℝ) - 1) ≠ 0 := by
      have h2 : (0 : ℝ) < 2 * (r : ℝ) - 1 := by linarith [hr2R]
      have heq : (1 : ℝ) - 1 / (2 * (r : ℝ) - 1) =
          (2 * (r : ℝ) - 2) / (2 * (r : ℝ) - 1) := by
        field_simp
        ring
      rw [heq]
      exact div_ne_zero (by linarith [hr2R]) (ne_of_gt h2)
    rw [hz_eq, hdR, div_eq_div_iff hden hr1]
    field_simp [hd1]
    ring
  have h := Real.sum_range_le_log_div hz0 hz1 8
  have hgoal : (logSeries15 1 dd : ℝ) =
      ∑ i ∈ Finset.range 8,
        ((S * 2 * 1 ^ (2 * i + 1) / ((2 * i + 1) * dd ^ (2 * i + 1)) : ℕ) : ℝ) := by
    rw [logSeries15_eq]
    simp only [logTerm15]
    push_cast
    rfl
  have hterm : ∀ i, ((S * 2 * 1 ^ (2 * i + 1) /
        ((2 * i + 1) * dd ^ (2 * i + 1)) : ℕ) : ℝ) ≤
      (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
    intro i
    calc ((S * 2 * (1 : ℕ) ^ (2 * i + 1) /
          ((2 * i + 1) * dd ^ (2 * i + 1)) : ℕ) : ℝ)
        ≤ ((S * 2 * (1 : ℕ) ^ (2 * i + 1) : ℕ) : ℝ) /
            (((2 * i + 1) * dd ^ (2 * i + 1) : ℕ) : ℝ) := AxlerTheta.cast_div_le_real
      _ = ((S : ℝ) * 2 * (1 : ℝ) ^ (2 * i + 1)) /
            (((2 * i + 1) : ℝ) * (dd : ℝ) ^ (2 * i + 1)) := by push_cast; ring
      _ = (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
          have h2i1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hz_eq, one_div, inv_pow, one_pow]
          field_simp [hdpos.ne', h2i1]
  calc (logSeries15 1 dd : ℝ)
      = ∑ i ∈ Finset.range 8,
          ((S * 2 * 1 ^ (2 * i + 1) / ((2 * i + 1) * dd ^ (2 * i + 1)) : ℕ) : ℝ) := hgoal
    _ ≤ ∑ i ∈ Finset.range 8, (S : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = (S : ℝ) * 2 * (∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ (S : ℝ) * (Real.log r - Real.log (r - 1)) := by
        have h2 : (2 : ℝ) * (∑ i ∈ Finset.range 8,
            z ^ (2 * i + 1) / (2 * i + 1)) ≤
            Real.log r - Real.log ((r : ℝ) - 1) := by
          have h' := h
          rw [hratio, Real.log_div (by positivity : (r : ℝ) ≠ 0) hr1pos.ne'] at h'
          linarith only [h']
        calc (S : ℝ) * 2 * (∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1))
            = (S : ℝ) * (2 * (∑ i ∈ Finset.range 8,
                z ^ (2 * i + 1) / (2 * i + 1))) := by ring
          _ ≤ (S : ℝ) * (Real.log r - Real.log (r - 1)) :=
              mul_le_mul_of_nonneg_left h2 (by norm_num [S])

theorem incrOf_le_log (a b : ℕ) (ds : List ℕ)
    (ha : 2 ≤ a) (hab : a < b) (h64 : b < 2 ^ 64)
    (hds : ds.Nodup) (hpos : ∀ d ∈ ds, 1 ≤ d) (hle : ∀ d ∈ ds, d ≤ b - a)
    (hprime : ∀ d ∈ ds, Nat.Prime (a + d))
    (hcover : ∀ p, Nat.Prime p → a < p → p ≤ b → p - a ∈ ds) :
    (incrOf (moments ds) a b : ℝ) ≤ (S : ℝ) * (logProd b - logProd a) := by
  have hb : a ≤ b := le_of_lt hab
  by_cases hcnt : (moments ds).count = 1
  · have hlen : ds.length = 1 := hcnt
    obtain ⟨d, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hmem : d ∈ [d] := List.mem_singleton.mpr rfl
    have hd1 : 1 ≤ d := hpos d hmem
    have hdle : d ≤ b - a := hle d hmem
    have hpr : Nat.Prime (a + d) := hprime d hmem
    set r := a + d with hr
    have hr2 : 2 ≤ r := by omega
    have hrb : r ≤ b := by omega
    have hincr : incrOf (moments [d]) a b = logSeries15 1 (2 * (a + d) - 1) := by
      simp [incrOf, moments]
    rw [hincr, ← hr]
    have hseries := logSeries15_one_le_step r hr2
    have hlogsum : logProd b - logProd a = Real.log (1 + 1 / ((r : ℝ) - 1)) := by
      rw [sum_log_sdiff a b hb]
      have hset : Nat.primesLE b \ Nat.primesLE a = {r} := by
        ext p
        constructor
        · intro hp
          obtain ⟨hpb, hpa⟩ := Finset.mem_sdiff.mp hp
          obtain ⟨hpb', hpp⟩ := Nat.mem_primesLE.mp hpb
          have hap : a < p := by
            by_contra hc
            exact hpa (Nat.mem_primesLE.mpr ⟨by omega, hpp⟩)
          have hm : p - a ∈ [d] := hcover p hpp hap hpb'
          have hpd : p - a = d := List.mem_singleton.mp hm
          have : p = r := by omega
          simp [this]
        · intro hp
          rw [Finset.mem_singleton] at hp
          subst hp
          rw [Finset.mem_sdiff]
          constructor
          · exact Nat.mem_primesLE.mpr ⟨hrb, hpr⟩
          · intro hcontra
            have := (Nat.mem_primesLE.mp hcontra).1
            omega
      rw [hset, Finset.sum_singleton]
    have hratio : 1 + 1 / ((r : ℝ) - 1) = (r : ℝ) / ((r : ℝ) - 1) := by
      have h1 : ((r : ℝ) - 1) ≠ 0 := by
        have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
        linarith
      field_simp
      ring
    have hrne : (r : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
      linarith
    have hr1ne : ((r : ℝ) - 1) ≠ 0 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
      linarith
    calc ((logSeries15 1 (2 * r - 1) : ℕ) : ℝ)
        ≤ (S : ℝ) * (Real.log r - Real.log (r - 1)) := hseries
      _ = (S : ℝ) * (logProd b - logProd a) := by
          rw [hlogsum, hratio, Real.log_div hrne hr1ne]
  · have hiff : incrOf (moments ds) a b = blockNum (moments ds) a b := by
      simp only [incrOf, hcnt, if_false]
    rw [hiff]
    exact blockNum_le_log a b ds ha hab hds hpos hle hprime hcover

-- ============================================================
-- Part C2: block state advance and block range soundness
-- ============================================================

theorem primesLE_succ_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime (n + 1)) :
    Nat.primesLE (n + 1) = Nat.primesLE n := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨hpn, hpp⟩ := Nat.mem_primesLE.mp hp
    rcases eq_or_lt_of_le hpn with h | h
    · rw [h] at hpp
      exact absurd hpp hn
    · exact Nat.mem_primesLE.mpr ⟨by omega, hpp⟩
  · exact Nat.primesLE_mono (by omega)

theorem logProd_succ_prime {p : ℕ} (hp : Nat.Prime p) (h3 : 3 ≤ p) :
    logProd (p + 1) = logProd p := by
  have hps : Nat.primesLE (p + 1) = Nat.primesLE p := by
    apply primesLE_succ_of_not_prime
    intro hcon
    have hev : Even (p + 1) := by
      obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two hp (by omega)
      exact ⟨k + 1, by omega⟩
    have h2 : p + 1 = 2 := (Nat.Prime.even_iff hcon).mp hev
    exact hp.ne_one (by omega)
  simp only [logProd, eulerProduct, hps]

theorem logProd_succ_of_not_prime {n : ℕ} (hn : ¬ Nat.Prime (n + 1)) :
    logProd (n + 1) = logProd n := by
  simp only [logProd, eulerProduct, primesLE_succ_of_not_prime hn]

theorem logProd_two : logProd 2 = Real.log 2 := by
  have hset : Nat.primesLE 2 = {2} := by
    apply Finset.Subset.antisymm
    · intro p hp
      obtain ⟨hp2, hpp⟩ := Nat.mem_primesLE.mp hp
      rw [Finset.mem_singleton]
      exact le_antisymm hp2 hpp.two_le
    · intro p hp
      rw [Finset.mem_singleton] at hp
      subst hp
      exact Nat.mem_primesLE.mpr ⟨le_refl 2, Nat.prime_two⟩
  rw [logProd, eulerProduct, hset, Finset.prod_singleton]
  norm_num

theorem blk_state {gbase top m : ℕ} {B : Blk} {L L' : ℕ}
    (hm : m = mask gbase top) (h : blkSpec gbase m B L L')
    (hbase : gbase ≤ B.a) (hb1 : 1 ≤ gbase) (hsq : top ≤ gbase * gbase)
    (hbtop : B.b ≤ top) (h8 : B.b ≤ 10 ^ 8) (hlen : B.b - B.a ≤ 2 ^ 13)
    (ha2 : 2 ≤ B.a) (hab : B.a < B.b)
    (hL : (L : ℝ) ≤ (S : ℝ) * logProd B.a) :
    (L' : ℝ) ≤ (S : ℝ) * logProd B.b := by
  unfold blkSpec at h
  obtain ⟨hL'e, lhi, hhi, hlhi, hhhi, hlhi2, hlhi64, hsub, hentry⟩ := h
  set ds := ((List.range (B.b - B.a)).filter
    (fun i => decide (Nat.Prime (B.a + 1 + i)))).map (fun i => i + 1) with hdsdef
  have hwm := windowMoments_prime_offsets gbase top B.a B.b hbase hb1 hsq hab hbtop h8 hlen
  rw [← hdsdef, ← hm] at hwm
  have hds : ds.Nodup := by
    rw [hdsdef]
    exact List.Nodup.map (fun x y hxy => by omega) (List.Nodup.filter _ List.nodup_range)
  have hpos : ∀ d ∈ ds, 1 ≤ d := by
    intro d hd
    rw [hdsdef] at hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have := List.mem_range.mp (List.mem_of_mem_filter hi)
    omega
  have hle : ∀ d ∈ ds, d ≤ B.b - B.a := by
    intro d hd
    rw [hdsdef] at hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have := List.mem_range.mp (List.mem_of_mem_filter hi)
    omega
  have hprime : ∀ d ∈ ds, Nat.Prime (B.a + d) := by
    intro d hd
    rw [hdsdef] at hd
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hd
    have hdec := (List.mem_filter.mp hi).2
    have hp := of_decide_eq_true hdec
    have e : B.a + (i + 1) = B.a + 1 + i := by omega
    rwa [e]
  have hcover : ∀ p, Nat.Prime p → B.a < p → p ≤ B.b → p - B.a ∈ ds := by
    intro p hpp hap hpb
    rw [hdsdef]
    apply List.mem_map.mpr
    refine ⟨p - B.a - 1, ?_, by omega⟩
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    rw [decide_eq_true_iff]
    have e : B.a + 1 + (p - B.a - 1) = p := by omega
    rwa [e]
  have hb64 : B.b < 2 ^ 64 := by omega
  have hbl := incrOf_le_log B.a B.b ds ha2 hab hb64 hds hpos hle hprime hcover
  have hmono : (S : ℝ) * logProd B.a ≤ (S : ℝ) * logProd B.b :=
    mul_le_mul_of_nonneg_left (logProd_mono B.a B.b (le_of_lt hab))
      (by norm_num [S] : (0 : ℝ) ≤ S)
  rw [hL'e, Nat.cast_add, hwm]
  linarith [hL, hbl, hmono]

theorem blk_range {gbase m : ℕ} {B : Blk} {L L' : ℕ} {l0 : ℕ}
    (h : blkSpec gbase m B L L') (h2b : 2 ≤ B.b) (hb8 : B.b ≤ 10 ^ 8)
    (hl02 : 2 ≤ l0) (hL : (L : ℝ) ≤ (S : ℝ) * logProd l0)
    (hγ : Real.eulerMascheroniConstant < (gammaUpS : ℝ) / (S : ℝ)) :
    ∀ x : ℝ, (l0 : ℝ) ≤ x → x ≤ (B.b : ℝ) →
      Real.exp Real.eulerMascheroniConstant * Real.log x < eulerProduct ⌊x⌋₊ := by
  unfold blkSpec at h
  obtain ⟨hL'e, lhi, hhi, hlhi, hhhi, hlhi2, hlhi64, hsub, hentry⟩ := h
  have hlo2 : 2 ≤ logUp15 B.b := hlhi ▸ hlhi2
  have hlo64 : logUp15 B.b < 2 ^ 64 := hlhi ▸ hlhi64
  have hsub' : logLo15 S ≤ logUp15 (logUp15 B.b) := by
    rw [← hlhi, ← hhhi]
    exact hsub
  have hll := llUp_sound B.b h2b hb8 hlo2 hlo64 hsub'
  rw [← hlhi, ← hhhi] at hll
  have hcast : ((hhi - logLo15 S : ℕ) : ℝ) = (hhi : ℝ) - (logLo15 S : ℝ) :=
    Nat.cast_sub hsub
  rw [hcast] at hll
  have hentryR : (gammaUpS : ℝ) + ((hhi : ℝ) - (logLo15 S : ℝ)) < (L : ℝ) := by
    have h1 : ((gammaUpS + (hhi - logLo15 S) : ℕ) : ℝ) < (L : ℝ) := by exact_mod_cast hentry
    push_cast at h1
    rwa [hcast] at h1
  have hSpos : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hSγ : (S : ℝ) * Real.eulerMascheroniConstant < (gammaUpS : ℝ) := by
    calc (S : ℝ) * Real.eulerMascheroniConstant
        < (S : ℝ) * ((gammaUpS : ℝ) / (S : ℝ)) := mul_lt_mul_of_pos_left hγ hSpos
      _ = (gammaUpS : ℝ) := by field_simp
  intro x hx hxb
  have hx1 : 1 < x := by
    have : (2 : ℝ) ≤ (l0 : ℝ) := by exact_mod_cast hl02
    linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hb1R : 1 < (B.b : ℝ) := by exact_mod_cast (show 1 < B.b by omega)
  have hlogb : 0 < Real.log (B.b : ℝ) := Real.log_pos hb1R
  have hlogxb : Real.log x ≤ Real.log (B.b : ℝ) := Real.log_le_log hx0 hxb
  have hloglog : Real.log (Real.log x) ≤ Real.log (Real.log (B.b : ℝ)) :=
    Real.log_le_log hlogx hlogxb
  have hsum2 : (S : ℝ) * (Real.eulerMascheroniConstant +
      Real.log (Real.log (B.b : ℝ))) < (L : ℝ) := by
    have hdist : (S : ℝ) * (Real.eulerMascheroniConstant +
        Real.log (Real.log (B.b : ℝ))) =
        (S : ℝ) * Real.eulerMascheroniConstant +
          (S : ℝ) * Real.log (Real.log (B.b : ℝ)) := by ring
    rw [hdist]
    linarith only [hSγ, hll, hentryR]
  have hSx : (S : ℝ) * (Real.eulerMascheroniConstant + Real.log (Real.log x)) < (L : ℝ) := by
    have hle : Real.eulerMascheroniConstant + Real.log (Real.log x) ≤
        Real.eulerMascheroniConstant + Real.log (Real.log (B.b : ℝ)) := by linarith
    have hm := mul_le_mul_of_nonneg_left hle hSpos.le
    exact lt_of_le_of_lt hm hsum2
  have hlfloor : logProd l0 ≤ logProd ⌊x⌋₊ := logProd_mono l0 ⌊x⌋₊ (Nat.le_floor hx)
  have hSL : (S : ℝ) * (Real.eulerMascheroniConstant + Real.log (Real.log x)) <
      (S : ℝ) * logProd ⌊x⌋₊ := by
    have hm := mul_le_mul_of_nonneg_left hlfloor hSpos.le
    linarith only [hSx, hL, hm]
  have hfin : Real.eulerMascheroniConstant + Real.log (Real.log x) < logProd ⌊x⌋₊ :=
    lt_of_mul_lt_mul_left hSL hSpos.le
  calc Real.exp Real.eulerMascheroniConstant * Real.log x
      = Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log x)) := by
        rw [Real.exp_add, Real.exp_log hlogx]
    _ < Real.exp (logProd ⌊x⌋₊) := Real.exp_lt_exp.mpr hfin
    _ = eulerProduct ⌊x⌋₊ := by rw [logProd]; exact Real.exp_log (eulerProduct_pos _)

theorem state_range {p q L lhi hhi : ℕ}
    (hp2 : 2 ≤ p) (hq2 : 2 ≤ q) (hq8 : q ≤ 10 ^ 8)
    (hlhi : lhi = logUp15 q) (hhhi : hhi = logUp15 lhi)
    (hlhi2 : 2 ≤ lhi) (hlhi64 : lhi < 2 ^ 64) (hsub : logLo15 S ≤ hhi)
    (hentry : gammaUpS + (hhi - logLo15 S) < L)
    (hL : (L : ℝ) ≤ (S : ℝ) * logProd p)
    (hγ : Real.eulerMascheroniConstant < (gammaUpS : ℝ) / (S : ℝ)) :
    ∀ x : ℝ, (p : ℝ) ≤ x → x ≤ (q : ℝ) →
      Real.exp Real.eulerMascheroniConstant * Real.log x < eulerProduct ⌊x⌋₊ := by
  have hlo2 : 2 ≤ logUp15 q := hlhi ▸ hlhi2
  have hlo64 : logUp15 q < 2 ^ 64 := hlhi ▸ hlhi64
  have hsub' : logLo15 S ≤ logUp15 (logUp15 q) := by
    rw [← hlhi, ← hhhi]
    exact hsub
  have hll := llUp_sound q hq2 hq8 hlo2 hlo64 hsub'
  rw [← hlhi, ← hhhi] at hll
  have hcast : ((hhi - logLo15 S : ℕ) : ℝ) = (hhi : ℝ) - (logLo15 S : ℝ) :=
    Nat.cast_sub hsub
  rw [hcast] at hll
  have hentryR : (gammaUpS : ℝ) + ((hhi : ℝ) - (logLo15 S : ℝ)) < (L : ℝ) := by
    have h1 : ((gammaUpS + (hhi - logLo15 S) : ℕ) : ℝ) < (L : ℝ) := by exact_mod_cast hentry
    push_cast at h1
    rwa [hcast] at h1
  have hSpos : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hSγ : (S : ℝ) * Real.eulerMascheroniConstant < (gammaUpS : ℝ) := by
    calc (S : ℝ) * Real.eulerMascheroniConstant
        < (S : ℝ) * ((gammaUpS : ℝ) / (S : ℝ)) := mul_lt_mul_of_pos_left hγ hSpos
      _ = (gammaUpS : ℝ) := by field_simp
  intro x hx hxb
  have hx1 : 1 < x := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hb1R : 1 < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
    linarith
  have hlogb : 0 < Real.log (q : ℝ) := Real.log_pos hb1R
  have hlogxb : Real.log x ≤ Real.log (q : ℝ) := Real.log_le_log hx0 hxb
  have hloglog : Real.log (Real.log x) ≤ Real.log (Real.log (q : ℝ)) :=
    Real.log_le_log hlogx hlogxb
  have hsum2 : (S : ℝ) * (Real.eulerMascheroniConstant +
      Real.log (Real.log (q : ℝ))) < (L : ℝ) := by
    have hdist : (S : ℝ) * (Real.eulerMascheroniConstant +
        Real.log (Real.log (q : ℝ))) =
        (S : ℝ) * Real.eulerMascheroniConstant +
          (S : ℝ) * Real.log (Real.log (q : ℝ)) := by ring
    rw [hdist]
    linarith only [hSγ, hll, hentryR]
  have hSx : (S : ℝ) * (Real.eulerMascheroniConstant + Real.log (Real.log x)) < (L : ℝ) := by
    have hle : Real.eulerMascheroniConstant + Real.log (Real.log x) ≤
        Real.eulerMascheroniConstant + Real.log (Real.log (q : ℝ)) := by linarith
    have hm := mul_le_mul_of_nonneg_left hle hSpos.le
    exact lt_of_le_of_lt hm hsum2
  have hlfloor : logProd p ≤ logProd ⌊x⌋₊ := logProd_mono p ⌊x⌋₊ (Nat.le_floor hx)
  have hSL : (S : ℝ) * (Real.eulerMascheroniConstant + Real.log (Real.log x)) <
      (S : ℝ) * logProd ⌊x⌋₊ := by
    have hm := mul_le_mul_of_nonneg_left hlfloor hSpos.le
    linarith only [hSx, hL, hm]
  have hfin : Real.eulerMascheroniConstant + Real.log (Real.log x) < logProd ⌊x⌋₊ :=
    lt_of_mul_lt_mul_left hSL hSpos.le
  calc Real.exp Real.eulerMascheroniConstant * Real.log x
      = Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log x)) := by
        rw [Real.exp_add, Real.exp_log hlogx]
    _ < Real.exp (logProd ⌊x⌋₊) := Real.exp_lt_exp.mpr hfin
    _ = eulerProduct ⌊x⌋₊ := by rw [logProd]; exact Real.exp_log (eulerProduct_pos _)

-- ============================================================
-- Part C3: group chain state and range soundness
-- ============================================================

theorem grpSpec_state {G : Grp} {gbase m : ℕ} (hm : m = mask gbase G.top)
    (hbase1 : 1 ≤ gbase) (hbase2 : 2 ≤ gbase) (hsq : G.top ≤ gbase * gbase)
    (h8top : G.top ≤ 10 ^ 8) :
    ∀ prev L blks, grpSpec G gbase m prev L blks →
      (∀ B ∈ blks, gbase ≤ B.a ∧ B.a < B.b ∧ B.b ≤ G.top ∧
        B.b - B.a ≤ 2 ^ 13 ∧ B.b ≤ 10 ^ 8) →
      (L : ℝ) ≤ (S : ℝ) * logProd prev →
      (G.lfin : ℝ) ≤ (S : ℝ) * logProd G.top := by
  intro prev L blks
  induction blks generalizing prev L with
  | nil =>
    intro hspec _ hL
    simp only [grpSpec] at hspec
    obtain ⟨hprev, hLf⟩ := hspec
    subst hprev
    rw [← hLf]
    exact hL
  | cons B rest ih =>
    intro hspec hbd hL
    simp only [grpSpec] at hspec
    obtain ⟨hprev, L', hbs, hrest⟩ := hspec
    subst hprev
    have hB := hbd B (by simp)
    have hst := blk_state hm hbs hB.1 hbase1 hsq hB.2.2.1 hB.2.2.2.2
      hB.2.2.2.1 (le_trans hbase2 hB.1) hB.2.1 hL
    have hbd' : ∀ B' ∈ rest, gbase ≤ B'.a ∧ B'.a < B'.b ∧ B'.b ≤ G.top ∧
        B'.b - B'.a ≤ 2 ^ 13 ∧ B'.b ≤ 10 ^ 8 := by
      intro B' hB'
      exact hbd B' (List.mem_cons_of_mem B hB')
    exact ih B.b L' hrest hbd' hst

theorem grpSpec_range {G : Grp} {gbase m : ℕ} (hm : m = mask gbase G.top)
    (hbase1 : 1 ≤ gbase) (hbase2 : 2 ≤ gbase) (hsq : G.top ≤ gbase * gbase)
    (h8top : G.top ≤ 10 ^ 8)
    (hγ : Real.eulerMascheroniConstant < (gammaUpS : ℝ) / (S : ℝ)) :
    ∀ prev L blks, grpSpec G gbase m prev L blks →
      (∀ B ∈ blks, gbase ≤ B.a ∧ B.a < B.b ∧ B.b ≤ G.top ∧
        B.b - B.a ≤ 2 ^ 13 ∧ B.b ≤ 10 ^ 8) →
      (L : ℝ) ≤ (S : ℝ) * logProd prev →
      (G.lfin : ℝ) ≤ (S : ℝ) * logProd G.top ∧
        (∀ x : ℝ, (prev : ℝ) < x → x ≤ (G.top : ℝ) →
          Real.exp Real.eulerMascheroniConstant * Real.log x < eulerProduct ⌊x⌋₊) := by
  intro prev L blks
  induction blks generalizing prev L with
  | nil =>
    intro hspec _ hL
    simp only [grpSpec] at hspec
    obtain ⟨hprev, hLf⟩ := hspec
    subst hprev
    refine ⟨?_, ?_⟩
    · rw [← hLf]
      exact hL
    · intro x hx1 hx2
      exact absurd hx2 (not_le_of_gt hx1)
  | cons B rest ih =>
    intro hspec hbd hL
    simp only [grpSpec] at hspec
    obtain ⟨hprev, L', hbs, hrest⟩ := hspec
    subst hprev
    have hB := hbd B (by simp)
    have hst := blk_state hm hbs hB.1 hbase1 hsq hB.2.2.1 hB.2.2.2.2
      hB.2.2.2.1 (le_trans hbase2 hB.1) hB.2.1 hL
    have hbd' : ∀ B' ∈ rest, gbase ≤ B'.a ∧ B'.a < B'.b ∧ B'.b ≤ G.top ∧
        B'.b - B'.a ≤ 2 ^ 13 ∧ B'.b ≤ 10 ^ 8 := by
      intro B' hB'
      exact hbd B' (List.mem_cons_of_mem B hB')
    have hrec := ih B.b L' hrest hbd' hst
    refine ⟨hrec.1, ?_⟩
    intro x hx1 hx2
    by_cases hxb : x ≤ (B.b : ℝ)
    · exact blk_range hbs (by omega) hB.2.2.2.2 (le_trans hbase2 hB.1) hL hγ x
        (le_of_lt hx1) hxb
    · exact hrec.2 x (not_le.mp hxb) hx2

theorem grp_solution (G : Grp) (hOK : grpOK G = true) (hwf : grpWF G = true)
    (hγ : Real.eulerMascheroniConstant < (gammaUpS : ℝ) / (S : ℝ))
    (hstate : (G.lin : ℝ) ≤ (S : ℝ) * logProd G.lo) :
    (G.lfin : ℝ) ≤ (S : ℝ) * logProd G.top ∧
      (∀ x : ℝ, (G.lo : ℝ) < x → x ≤ (G.top : ℝ) →
        Real.exp Real.eulerMascheroniConstant * Real.log x < eulerProduct ⌊x⌋₊) := by
  have hP := grpWF_spec hwf
  have hbase2 : 2 ≤ G.base := by
    rcases hP.2.1 with hb | ⟨hbp, hb⟩ <;> omega
  have hbase1 : 1 ≤ G.base := by omega
  have hLbase : (G.lin : ℝ) ≤ (S : ℝ) * logProd G.base := by
    rcases hP.2.1 with hb | ⟨hbp, hb⟩
    · rw [hb]
      exact hstate
    · rw [hb, logProd_succ_prime hbp (by omega)]
      exact hstate
  have hspec := grpOK_spec hOK
  have hstatefin := grpSpec_state rfl hbase1 hbase2 hP.2.2.2.1 hP.2.2.2.2.1
    G.base G.lin G.blks hspec hP.2.2.2.2.2 hLbase
  refine ⟨hstatefin, ?_⟩
  cases hblks : G.blks with
  | nil =>
    exfalso
    rw [hblks] at hspec
    simp only [grpSpec] at hspec
    exact (ne_of_lt hP.2.2.1) hspec.1
  | cons B1 rest =>
    rw [hblks] at hspec
    simp only [grpSpec] at hspec
    obtain ⟨hprev, L1, hbs, hrest⟩ := hspec
    have hB1 := hP.2.2.2.2.2 B1 (by rw [hblks]; exact List.mem_cons_self)
    have hst1 := blk_state rfl hbs hB1.1 hbase1 hP.2.2.2.1 hB1.2.2.1 hB1.2.2.2.2
      hB1.2.2.2.1 (le_trans hbase2 hB1.1) hB1.2.1 (by rw [← hprev]; exact hLbase)
    have hbd' : ∀ B' ∈ rest, G.base ≤ B'.a ∧ B'.a < B'.b ∧ B'.b ≤ G.top ∧
        B'.b - B'.a ≤ 2 ^ 13 ∧ B'.b ≤ 10 ^ 8 := by
      intro B' hB'
      exact hP.2.2.2.2.2 B' (by rw [hblks]; exact List.mem_cons_of_mem B1 hB')
    have hrec := grpSpec_range rfl hbase1 hbase2 hP.2.2.2.1 hP.2.2.2.2.1 hγ
      B1.b L1 rest hrest hbd' hst1
    intro x hx1 hx2
    by_cases hxb : x ≤ (B1.b : ℝ)
    · exact blk_range hbs (by omega) hB1.2.2.2.2 (by omega : 2 ≤ G.lo) hstate hγ x
        (le_of_lt hx1) hxb
    · exact hrec.2 x (not_le.mp hxb) hx2

end RosserLower


