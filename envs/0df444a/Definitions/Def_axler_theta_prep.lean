-- Prove2me | Definitions.Def_axler_theta_prep
-- name    : axler_theta_prep
-- status  : Definition
-- author  : @andreaskapfer
-- created : 2026-10-01T16:52:42.006735+00:00
-- url     : https://prove2.me/theorems/2baae7ad-b400-4f38-a621-bdeb55a23aab
-- title:
--   Axler theta real-analysis preparation lemmas
-- statement:
--   Certificate infrastructure for the Rosser-Schoenfeld style theta bound chain (Axler).
-- source:
--   Axler, Elementary proof of the Chebyshev theta bounds, internal certificate modules.

import Definitions.Def_axler_theta_base

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset Real

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

open Finset Real
namespace AxlerTheta

open RosserBitSieve RosserScan RosserPackedBarrier RosserPrefixBridge

def scale : ℕ := 1000000

/-- Fuel-based binary logarithm: structural recursion, cheap in the kernel. -/
def log2f : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n < 2 then 0 else log2f f (n / 2) + 1

def log2k (n : ℕ) : ℕ := log2f 64 n

def logTerm (a d i : ℕ) : ℕ :=
  scale * 2 * a ^ (2 * i + 1) / ((2 * i + 1) * d ^ (2 * i + 1))

def logSeries (a d : ℕ) : ℕ := ((List.range 8).map (logTerm a d)).sum

lemma logSeries_eq (a d : ℕ) :
    logSeries a d = ∑ i ∈ Finset.range 8, logTerm a d i := by
  rw [logSeries, ← List.sum_toFinset (logTerm a d) (List.nodup_range (n := 8))]
  rfl

def logTermUp (a d i : ℕ) : ℕ :=
  (scale * 2 * a ^ (2 * i + 1)) ⌈/⌉ ((2 * i + 1) * d ^ (2 * i + 1))

def logSeriesUp (a d : ℕ) : ℕ := ((List.range 8).map (logTermUp a d)).sum

lemma logSeriesUp_eq (a d : ℕ) :
    logSeriesUp a d = ∑ i ∈ Finset.range 8, logTermUp a d i := by
  rw [logSeriesUp, ← List.sum_toFinset (logTermUp a d) (List.nodup_range (n := 8))]
  rfl

lemma log2f_zero : ∀ f, log2f f 0 = 0 := by
  intro f
  cases f with
  | zero => rfl
  | succ f => simp [log2f]

lemma log2f_one : ∀ f, log2f f 1 = 0 := by
  intro f
  cases f with
  | zero => rfl
  | succ f => simp [log2f]

lemma pow_log2f_le : ∀ f n, 2 ≤ n → n < 2 ^ f → 2 ^ log2f f n ≤ n := by
  intro f
  induction f with
  | zero =>
    intro n hn h
    norm_num at h
    omega
  | succ f ih =>
    intro n hn h
    rw [log2f]
    split_ifs with h2
    · omega
    · rw [Nat.pow_succ]
      by_cases hsmall : n / 2 < 2
      · have hz : log2f f (n / 2) = 0 := by
          have hc : n / 2 = 0 ∨ n / 2 = 1 := by omega
          rcases hc with hc | hc
          · rw [hc]
            exact log2f_zero f
          · rw [hc]
            exact log2f_one f
        rw [hz]
        norm_num
        omega
      · have hn2 : 2 ≤ n / 2 := by omega
        have hlt : n / 2 < 2 ^ f := by
          rw [pow_succ] at h
          exact (Nat.div_lt_iff_lt_mul (k := 2) (x := n) (y := 2 ^ f)
            (by norm_num)).2 h
        have hih := ih (n / 2) hn2 hlt
        calc 2 ^ (log2f f (n / 2) + 1) = 2 * 2 ^ log2f f (n / 2) := by
              rw [pow_succ]
              ring
          _ ≤ 2 * (n / 2) := by omega
          _ ≤ n := by omega

def logLoNum (n : ℕ) : ℕ :=
  let k := log2k n
  let q := 2 ^ k
  let a := n - q
  let d := n + q
  k * 6931471803 / 10000 + logSeries a d

def logUpNum (n : ℕ) : ℕ :=
  let k := log2k n
  let q := 2 ^ k
  let a := n - q
  let d := n + q
  (k * 6931471808) ⌈/⌉ 10000 + logSeriesUp a d +
    (scale * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2))

lemma cast_div_le_real {x m : ℕ} : ((x / m : ℕ) : ℝ) ≤ (x : ℝ) / m := Nat.cast_div_le

lemma real_div_le_cast_ceilDiv {x m : ℕ} (hm : 0 < m) :
    (x : ℝ) / m ≤ ((x ⌈/⌉ m : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_le_iff₀ hmR]
  have h : x ≤ m * (x ⌈/⌉ m) := by
    simpa using le_smul_ceilDiv hm (b := x)
  have h' : (x : ℝ) ≤ (m : ℝ) * ((x ⌈/⌉ m : ℕ) : ℝ) := by exact_mod_cast h
  linarith [h']

theorem logLoNum_sound (n : ℕ) (hn : 2 ≤ n) (hbig : n < 2 ^ 64) :
    (logLoNum n : ℝ) ≤ (scale : ℝ) * Real.log n := by
  set k := log2k n with hk
  set q := 2 ^ k with hq
  have hqle : q ≤ n := by
    rw [hq, hk, log2k]
    exact pow_log2f_le 64 n hn hbig
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
  have hgoal : (logLoNum n : ℝ) =
      ((k * 6931471803 / 10000 : ℕ) : ℝ) +
        ∑ i ∈ Finset.range 8,
          ((scale * 2 * a ^ (2 * i + 1) / ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) := by
    simp only [logLoNum, ← hk, ← hq, ← ha, ← hd]
    rw [logSeries_eq]
    simp only [logTerm]
    push_cast
    rfl
  have hK : ((k * 6931471803 / 10000 : ℕ) : ℝ) ≤
      (scale : ℝ) * ((k : ℝ) * Real.log 2) := by
    have h2 := Real.log_two_gt_d9.le
    calc ((k * 6931471803 / 10000 : ℕ) : ℝ)
        ≤ ((k * 6931471803 : ℕ) : ℝ) / 10000 := cast_div_le_real
      _ = (k : ℝ) * 6931471803 / 10000 := by push_cast; ring
      _ = (scale : ℝ) * ((k : ℝ) * (0.6931471803 : ℝ)) := by
          rw [show (0.6931471803 : ℝ) = 6931471803 / 10000000000 by norm_num]
          norm_num [scale]
          ring
      _ = (scale : ℝ) * (k : ℝ) * (0.6931471803 : ℝ) := by ring
      _ ≤ (scale : ℝ) * (k : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (by norm_num [scale])
            (Nat.cast_nonneg k))
      _ = (scale : ℝ) * ((k : ℝ) * Real.log 2) := by ring
  have hterm : ∀ i, ((scale * 2 * a ^ (2 * i + 1) /
        ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) ≤
      (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
    intro i
    calc ((scale * 2 * a ^ (2 * i + 1) /
          ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)
        ≤ ((scale * 2 * a ^ (2 * i + 1) : ℕ) : ℝ) /
            (((2 * i + 1) * d ^ (2 * i + 1) : ℕ) : ℝ) := cast_div_le_real
      _ = ((scale : ℝ) * 2 * (a : ℝ) ^ (2 * i + 1)) /
            (((2 * i + 1) : ℝ) * (d : ℝ) ^ (2 * i + 1)) := by push_cast; ring
      _ = (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) := by
          have h2i1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', h2i1]
  have hsum : (∑ i ∈ Finset.range 8,
        ((scale * 2 * a ^ (2 * i + 1) /
          ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) ≤
      (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) := by
    calc (∑ i ∈ Finset.range 8, ((scale * 2 * a ^ (2 * i + 1) /
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ))
        ≤ ∑ i ∈ Finset.range 8,
            (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = (scale : ℝ) * 2 * (∑ i ∈ Finset.range 8,
            z ^ (2 * i + 1) / (2 * i + 1)) := by
          rw [Finset.mul_sum]
      _ ≤ (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) := by
          have h2 : (2 : ℝ) * (∑ i ∈ Finset.range 8,
              z ^ (2 * i + 1) / (2 * i + 1)) ≤
              Real.log n - (k : ℝ) * Real.log 2 := by linarith only [h]
          calc (scale : ℝ) * 2 * (∑ i ∈ Finset.range 8,
                z ^ (2 * i + 1) / (2 * i + 1))
              = (scale : ℝ) * (2 * (∑ i ∈ Finset.range 8,
                z ^ (2 * i + 1) / (2 * i + 1))) := by ring
            _ ≤ (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) :=
                mul_le_mul_of_nonneg_left h2 (by norm_num [scale])
  rw [hgoal]
  have hfinal : (scale : ℝ) * ((k : ℝ) * Real.log 2) +
      (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) =
      (scale : ℝ) * Real.log n := by ring
  linarith only [hK, hsum, hfinal]

theorem logUpNum_sound (n : ℕ) (hn : 2 ≤ n) (hbig : n < 2 ^ 64) :
    (scale : ℝ) * Real.log n ≤ (logUpNum n : ℝ) := by
  set k := log2k n with hk
  set q := 2 ^ k with hq
  have hqle : q ≤ n := by
    rw [hq, hk, log2k]
    exact pow_log2f_le 64 n hn hbig
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
  have hgoal : (logUpNum n : ℝ) =
      (((k * 6931471808) ⌈/⌉ 10000 : ℕ) : ℝ) +
        (∑ i ∈ Finset.range 8,
          (((scale * 2 * a ^ (2 * i + 1)) ⌈/⌉
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) +
        (((scale * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
    simp only [logUpNum, ← hk, ← hq, ← ha, ← hd]
    rw [logSeriesUp_eq]
    simp only [logTermUp]
    push_cast
    rfl
  have hK : (scale : ℝ) * ((k : ℝ) * Real.log 2) ≤
      (((k * 6931471808) ⌈/⌉ 10000 : ℕ) : ℝ) := by
    have h2 := Real.log_two_lt_d9.le
    calc (scale : ℝ) * ((k : ℝ) * Real.log 2)
        ≤ (scale : ℝ) * ((k : ℝ) * (0.6931471808 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num [scale])
          exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
      _ = (k : ℝ) * 6931471808 / 10000 := by
          rw [show (0.6931471808 : ℝ) = 6931471808 / 10000000000 by norm_num]
          norm_num [scale]
          ring
      _ = ((k * 6931471808 : ℕ) : ℝ) / 10000 := by push_cast; ring
      _ ≤ (((k * 6931471808) ⌈/⌉ 10000 : ℕ) : ℝ) :=
          real_div_le_cast_ceilDiv (by norm_num)
  have hterm : ∀ i, (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1)) ≤
      (((scale * 2 * a ^ (2 * i + 1)) ⌈/⌉
        ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) := by
    intro i
    calc (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))
        = ((scale : ℝ) * 2 * (a : ℝ) ^ (2 * i + 1)) /
            (((2 * i + 1) : ℝ) * (d : ℝ) ^ (2 * i + 1)) := by
          have h2i1 : ((2 * i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', h2i1]
      _ = ((scale * 2 * a ^ (2 * i + 1) : ℕ) : ℝ) /
            (((2 * i + 1) * d ^ (2 * i + 1) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((scale * 2 * a ^ (2 * i + 1)) ⌈/⌉
            ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ) :=
          real_div_le_cast_ceilDiv (by positivity)
  have htail : (scale : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2))) ≤
      (((scale * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
    have hd2a2R : (0 : ℝ) < (d : ℝ) ^ 2 - (a : ℝ) ^ 2 := by
      have hle : a ^ 2 ≤ d ^ 2 := le_of_lt (by omega : a ^ 2 < d ^ 2)
      rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_sub hle]
      exact_mod_cast hd2a2
    calc (scale : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2)))
        = (scale : ℝ) * 2 * (a : ℝ) ^ 17 /
            ((d : ℝ) ^ 15 * ((d : ℝ) ^ 2 - (a : ℝ) ^ 2)) := by
          rw [hz_eq, div_pow]
          field_simp [hdpos.ne', hd2a2R.ne']
      _ ≤ (((scale * 2 * a ^ 17) ⌈/⌉
            (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
          have hle : a ^ 2 ≤ d ^ 2 := by omega
          have h := real_div_le_cast_ceilDiv (x := scale * 2 * a ^ 17)
            (m := d ^ 15 * (d ^ 2 - a ^ 2)) (by positivity)
          push_cast [Nat.cast_sub hle] at h
          exact h
  have hsplit : (scale : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
        z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) =
      (∑ i ∈ Finset.range 8,
        (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))) +
      (scale : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2))) := by
    rw [show (scale : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
          z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) =
        (scale : ℝ) * 2 * (∑ i ∈ Finset.range 8,
          z ^ (2 * i + 1) / (2 * i + 1)) +
        (scale : ℝ) * 2 * (z ^ 17 / (1 - z ^ 2)) from by ring]
    rw [Finset.mul_sum]
    ring
  have h2 : (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) ≤
      (scale : ℝ) * (2 * ((∑ i ∈ Finset.range 8,
        z ^ (2 * i + 1) / (2 * i + 1)) + z ^ 17 / (1 - z ^ 2))) := by
    have h' : (1 : ℝ) / 2 * (Real.log n - (k : ℝ) * Real.log 2) ≤
        (∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) +
          z ^ 17 / (1 - z ^ 2) := h
    have h2' : Real.log n - (k : ℝ) * Real.log 2 ≤
        2 * ((∑ i ∈ Finset.range 8, z ^ (2 * i + 1) / (2 * i + 1)) +
          z ^ 17 / (1 - z ^ 2)) := by linarith only [h']
    have hs0 : (0 : ℝ) ≤ (scale : ℝ) := by norm_num [scale]
    exact mul_le_mul_of_nonneg_left h2' hs0
  rw [hgoal]
  have hbound :
      (scale : ℝ) * ((k : ℝ) * Real.log 2) +
          (∑ i ∈ Finset.range 8, (scale : ℝ) * 2 * (z ^ (2 * i + 1) / (2 * i + 1))) +
          ((scale : ℝ) * (2 * (z ^ 17 / (1 - z ^ 2)))) ≤
      (((k * 6931471808) ⌈/⌉ 10000 : ℕ) : ℝ) +
          (∑ i ∈ Finset.range 8,
            (((scale * 2 * a ^ (2 * i + 1)) ⌈/⌉
              ((2 * i + 1) * d ^ (2 * i + 1)) : ℕ) : ℝ)) +
          (((scale * 2 * a ^ 17) ⌈/⌉ (d ^ 15 * (d ^ 2 - a ^ 2)) : ℕ) : ℝ) := by
    exact add_le_add
      (add_le_add hK (Finset.sum_le_sum (fun i _ => hterm i)))
      htail
  rw [hsplit] at h2
  have hfinal : (scale : ℝ) * ((k : ℝ) * Real.log 2) +
      (scale : ℝ) * (Real.log n - (k : ℝ) * Real.log 2) =
      (scale : ℝ) * Real.log n := by ring
  linarith only [h2, hbound, hfinal]

end AxlerTheta

namespace AxlerTheta

open RosserBitSieve RosserBitMoments RosserPackedMoments RosserScan

def countBytes (mask stripe : ℕ) : ℕ → ℕ → ℕ
  | 0, total => total
  | j + 1, total =>
    forceNat ((mask >>> j) &&& stripe) fun bit =>
      forceNat (total + bit) (countBytes mask stripe j)

def countCombine (bits half count : ℕ) : ℕ :=
  let stripe := periodicMask (2 * half) (bits / (2 * half)) * (2 ^ half - 1)
  forceNat stripe fun stripe => (count &&& stripe) + ((count >>> half) &&& stripe)

def countReduce (bits : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, total => total
  | fuel + 1, half, total =>
    forceNat (countCombine bits half total) (countReduce bits fuel (2 * half))

def fastCount (depth mask : ℕ) : ℕ :=
  let bits := 2 ^ (depth + 3)
  forceNat (periodicMask 8 (bits / 8)) fun stripe =>
    forceNat (countBytes mask stripe 8 0) (countReduce bits depth 8)

lemma countBytes_eq (mask stripe j : ℕ) (state : Moments) :
    countBytes mask stripe j state.count = (bytes mask stripe j state).count := by
  induction j generalizing state with
  | zero => rfl
  | succ j ih =>
    simp only [countBytes, bytes, forceNat_eq, strictMoments_eq]
    exact ih ⟨state.count + ((mask >>> j) &&& stripe),
      state.first + j * ((mask >>> j) &&& stripe),
      state.second + j * j * ((mask >>> j) &&& stripe)⟩

lemma countCombine_eq (bits half : ℕ) (state : Moments) :
    countCombine bits half state.count = (combine bits half state).count := by
  simp only [countCombine, combine, forceNat_eq]

lemma countReduce_eq (bits fuel half : ℕ) (state : Moments) :
    countReduce bits fuel half state.count = (reduce bits fuel half state).count := by
  induction fuel generalizing half state with
  | zero => rfl
  | succ fuel ih =>
    simp only [countReduce, reduce, forceNat_eq, strictMoments_eq, countCombine_eq]
    exact ih _ _

lemma fastCount_eq (depth mask : ℕ) : fastCount depth mask = (packedMoments depth mask).count := by
  simp only [fastCount, packedMoments, forceNat_eq, strictMoments_eq, translate]
  rw [show countBytes mask (periodicMask 8 (2 ^ (depth + 3) / 8)) 8 0 =
    (bytes mask (periodicMask 8 (2 ^ (depth + 3) / 8)) 8 ⟨0, 0, 0⟩).count from
      countBytes_eq _ _ _ ⟨0, 0, 0⟩]
  exact countReduce_eq _ _ _ _

def bitCount (depth mask : ℕ) : ℕ :=
  forceNat mask fun value => fastCount depth value

lemma bitCount_sound (depth mask len : ℕ) (hm : mask < 2 ^ len)
    (hlen : len ≤ 2 ^ (depth + 3)) :
    bitCount depth mask = RosserPackedBarrier.candidateCount mask len := by
  rw [bitCount, forceNat_eq, fastCount_eq, packedMoments_sound depth mask
    (hm.trans_le (Nat.pow_le_pow_right (by norm_num) hlen))]
  exact (candidateCount_eq_enumBits_length depth mask len hm hlen).symm

lemma depthFor_covers (len : ℕ) : len ≤ 2 ^ (RosserFastCompute.depthFor len + 3) := by
  unfold RosserFastCompute.depthFor
  split_ifs with h
  · norm_num
    exact h
  · rw [pow_add]
    norm_num only [Nat.reducePow]
    have ht := Nat.lt_log2_self (n := (len - 1) / 8)
    omega

end AxlerTheta

namespace AxlerTheta

open RosserProductCertificate

def anchorLo : ℕ := 9895967639
def anchorHi : ℕ := 9896137436

theorem anchor_lo_raw : anchorLo ≤ ((RosserProductCertificate.referencePrimes 9973).map logLoNum).sum := by
  decide +kernel

theorem anchor_hi_raw : ((RosserProductCertificate.referencePrimes 9973).map logUpNum).sum ≤ anchorHi := by
  decide +kernel


lemma list_sum_cast_real (l : List ℕ) (f : ℕ → ℕ) :
    (Nat.cast ((l.map f).sum) : ℝ) = (l.map (fun p => (f p : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem anchor_lo_sound :
    (anchorLo : ℝ) ≤ (scale : ℝ) * Chebyshev.theta ((9973 : ℕ) : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hraw := anchor_lo_raw
  have hcast : (anchorLo : ℝ) ≤
      ((RosserProductCertificate.referencePrimes 9973).map (fun p => (logLoNum p : ℝ))).sum := by
    rw [← list_sum_cast_real (RosserProductCertificate.referencePrimes 9973) logLoNum]
    exact_mod_cast hraw
  have hlist : ((RosserProductCertificate.referencePrimes 9973).map (fun p => (logLoNum p : ℝ))).sum ≤
      (scale : ℝ) * ∑ p ∈ Nat.primesLE 9973, Real.log (p : ℝ) := by
    rw [← List.sum_toFinset (fun p => (logLoNum p : ℝ)) (RosserProductCertificate.referencePrimes_nodup 9973)]
    rw [RosserProductCertificate.referencePrimes_toFinset 9973]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hmem : p ≤ 9973 ∧ Nat.Prime p := Nat.mem_primesLE.mp hp
    exact logLoNum_sound p hmem.2.two_le
      (lt_of_le_of_lt hmem.1 (by norm_num))
  exact hcast.trans hlist

theorem anchor_hi_sound :
    (scale : ℝ) * Chebyshev.theta ((9973 : ℕ) : ℝ) ≤ (anchorHi : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hraw := anchor_hi_raw
  have hcast : ((RosserProductCertificate.referencePrimes 9973).map (fun p => (logUpNum p : ℝ))).sum ≤
      (anchorHi : ℝ) := by
    rw [← list_sum_cast_real (RosserProductCertificate.referencePrimes 9973) logUpNum]
    exact_mod_cast hraw
  have hlist : (scale : ℝ) * ∑ p ∈ Nat.primesLE 9973, Real.log (p : ℝ) ≤
      ((RosserProductCertificate.referencePrimes 9973).map (fun p => (logUpNum p : ℝ))).sum := by
    rw [Finset.mul_sum]
    rw [← List.sum_toFinset (fun p => (logUpNum p : ℝ)) (RosserProductCertificate.referencePrimes_nodup 9973)]
    rw [RosserProductCertificate.referencePrimes_toFinset 9973]
    refine Finset.sum_le_sum (fun p hp => ?_)
    have hmem : p ≤ 9973 ∧ Nat.Prime p := Nat.mem_primesLE.mp hp
    exact logUpNum_sound p hmem.2.two_le
      (lt_of_le_of_lt hmem.1 (by norm_num))
  exact hlist.trans hcast

end AxlerTheta

namespace AxlerTheta

open RosserBitSieve RosserScan RosserPackedBarrier

theorem theta_eq_of_no_primes (a n : ℕ) (han : a ≤ n)
    (h : ∀ p, Nat.Prime p → a < p → p ≤ n → False) :
    Chebyshev.theta n = Chebyshev.theta a := by
  have hset : Nat.primesLE n = Nat.primesLE a := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hpn, hp⟩
      by_cases hpa : p ≤ a
      · exact ⟨hpa, hp⟩
      · exact (h p hp (by omega) hpn).elim
    · rintro ⟨hpa, hp⟩
      exact ⟨hpa.trans han, hp⟩
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hset]

theorem theta_eq_add_prime (a p : ℕ) (hp : Nat.Prime p) (hap : a < p)
    (h : ∀ q, Nat.Prime q → a < q → q < p → False) :
    Chebyshev.theta p = Chebyshev.theta a + Real.log p := by
  have hset : Nat.primesLE p = insert p (Nat.primesLE a) := by
    ext q
    simp only [Nat.mem_primesLE, Finset.mem_insert]
    constructor
    · rintro ⟨hqp, hq⟩
      by_cases hqa : q ≤ a
      · exact Or.inr ⟨hqa, hq⟩
      · left
        by_contra hne
        exact h q hq (by omega) (by omega)
    · rintro (rfl | ⟨hqa, hq⟩)
      · exact ⟨le_rfl, hp⟩
      · exact ⟨hqa.trans (by omega), hq⟩
  have hnot : p ∉ Nat.primesLE a := by
    simp only [Nat.mem_primesLE, not_and]
    intro hp'
    omega
  rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hset,
    Finset.sum_insert hnot]
  ring

end AxlerTheta
-- ============================================================
-- Part 2: exactness of the sieve mask (candidates = primes)
-- ============================================================

namespace AxlerSieve

open RosserBitSieve RosserSieveData RosserProductCertificate

theorem divisors_eq_reference :
    RosserSieveData.divisors = RosserProductCertificate.referencePrimes 10000 := by
  decide +kernel

theorem referencePrimes_mem (B p : ℕ) :
    p ∈ RosserProductCertificate.referencePrimes B ↔ p ≤ B ∧ Nat.Prime p := by
  simp [RosserProductCertificate.referencePrimes, Nat.prime_def_minFac]

theorem divisors_cover (q : ℕ) (hq : Nat.Prime q) (hle : q ≤ 10000) :
    q ∈ RosserSieveData.divisors := by
  rw [divisors_eq_reference, referencePrimes_mem]
  exact ⟨hle, hq⟩

theorem periodicMask_bit_iff (d count i : ℕ) (hd : 0 < d) (hi : i < d * count) :
    (periodicMask d count).testBit i = true ↔ d ∣ i := by
  induction count generalizing i with
  | zero => omega
  | succ count ih =>
    rw [periodicMask_succ d count hd]
    rw [Nat.testBit_two_pow_mul_add (periodicMask d count) (b := 1) (i := d)
      (Nat.one_lt_two_pow (Nat.ne_of_gt hd)) i]
    by_cases hj : i < d
    · rw [if_pos hj]
      have hone : (1 : ℕ).testBit i = decide (i = 0) := by
        simpa only [Nat.pow_zero, eq_comm] using (Nat.testBit_two_pow (n := 0) (m := i))
      rw [hone, decide_eq_true_eq]
      constructor
      · intro h
        subst h
        exact dvd_zero d
      · intro hdiv
        exact Nat.eq_zero_of_dvd_of_lt hdiv hj
    · rw [if_neg hj]
      have hdlei : d ≤ i := by omega
      have hlt : i - d < d * count := by
        have : i < d * count + d := by
          rw [← Nat.mul_succ]
          exact hi
        omega
      rw [ih (i - d) hlt]
      constructor
      · intro hdiv
        have heq : i = (i - d) + d := by omega
        rw [heq]
        exact dvd_add hdiv (dvd_refl d)
      · intro hdiv
        exact Nat.dvd_sub hdiv (dvd_refl d)

theorem divisorMask_bit_iff (a len d i : ℕ) (hd : 0 < d) (hi : i < len) :
    (divisorMask a len d).testBit i = true ↔ d ∣ a + i := by
  have hlt : i < d * ((len + d - 1) / d) := by
    have hmod := Nat.div_add_mod (len + d - 1) d
    have hr := Nat.mod_lt (len + d - 1) hd
    omega
  unfold divisorMask
  rw [Nat.testBit_mul_two_pow, Bool.and_eq_true, decide_eq_true_eq]
  set s := (d - a % d) % d
  have hslt : s < d := Nat.mod_lt _ hd
  have hfirst : d ∣ a + s := first_multiple a d hd
  constructor
  · rintro ⟨hsi, hbit⟩
    have hp := (periodicMask_bit_iff d ((len + d - 1) / d) (i - s) hd (by omega)).mp hbit
    have heq : a + i = (a + s) + (i - s) := by omega
    rw [heq]
    exact dvd_add hfirst hp
  · intro hdiv
    have hsi : s ≤ i := by
      by_contra h
      have hsub : d ∣ (a + s) - (a + i) := Nat.dvd_sub hfirst hdiv
      have heq : (a + s) - (a + i) = s - i := by omega
      rw [heq] at hsub
      have hpos : 0 < s - i := by omega
      have hlt2 : s - i < d := by omega
      exact absurd (Nat.eq_zero_of_dvd_of_lt hsub hlt2) (Nat.ne_of_gt hpos)
    refine ⟨hsi, ?_⟩
    apply (periodicMask_bit_iff d ((len + d - 1) / d) (i - s) hd (by omega)).mpr
    have hsub : d ∣ (a + i) - (a + s) := Nat.dvd_sub hdiv hfirst
    have heq : (a + i) - (a + s) = i - s := by omega
    rwa [heq] at hsub

theorem foldl_or_testBit_false_imp (divisors : List ℕ) (a len acc i : ℕ)
    (h : (divisors.foldl (fun mask d => mask ||| divisorMask a len d) acc).testBit i = false) :
    acc.testBit i = false := by
  induction divisors generalizing acc with
  | nil => simpa using h
  | cons d ds ih =>
    rw [List.foldl_cons] at h
    have h' := ih (acc ||| divisorMask a len d) h
    rw [Nat.testBit_or, Bool.or_eq_false_iff] at h'
    exact h'.1

theorem foldl_or_mem_false (divisors : List ℕ) (a len d i : ℕ) (hd : d ∈ divisors)
    {acc : ℕ} (hacc : acc.testBit i = false)
    (h : (divisors.foldl (fun mask d => mask ||| divisorMask a len d) acc).testBit i = false) :
    (divisorMask a len d).testBit i = false := by
  induction divisors generalizing acc with
  | nil => simp at hd
  | cons e es ih =>
    rw [List.foldl_cons] at h
    have hhead : (divisorMask a len e).testBit i = false := by
      have h' := foldl_or_testBit_false_imp es a len (acc ||| divisorMask a len e) i h
      rw [Nat.testBit_or, Bool.or_eq_false_iff] at h'
      exact h'.2
    by_cases hde : d = e
    · rwa [hde]
    · have he : (acc ||| divisorMask a len e).testBit i = false :=
        foldl_or_testBit_false_imp es a len (acc ||| divisorMask a len e) i h
      have hd' : d ∈ es := by
        rcases List.mem_cons.mp hd with hh | hh
        · exact absurd hh hde
        · exact hh
      exact ih hd' he h

theorem candidateMask_not_dvd (divisors : List ℕ) (a len d i : ℕ)
    (hd2 : ∀ d ∈ divisors, 2 ≤ d) (hdm : d ∈ divisors) (hi : i < len)
    (hbit : (candidateMask divisors a len).testBit i = true) :
    ¬ d ∣ a + i := by
  intro hdiv
  have hdpos : 0 < d := by
    have := hd2 d hdm
    omega
  have hdmbit : (divisorMask a len d).testBit i = true :=
    (divisorMask_bit_iff a len d i hdpos hi).mpr hdiv
  have hcomp : (compositeMask divisors a len).testBit i = false := by
    rw [candidateMask_bit, Bool.and_eq_true] at hbit
    simpa using hbit.2
  have hfalse := foldl_or_mem_false divisors a len d i hdm (by simp) hcomp
  rw [hdmbit] at hfalse
  exact Bool.noConfusion hfalse

theorem exists_prime_le_sqrt {n : ℕ} (hn2 : 2 ≤ n) (hnp : ¬ Nat.Prime n) :
    ∃ q, Nat.Prime q ∧ q ∣ n ∧ q ≤ Nat.sqrt n := by
  refine ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n, ?_⟩
  rw [Nat.le_sqrt]
  simpa only [pow_two] using Nat.minFac_sq_le_self (by omega) hnp

theorem candidateMask_bit_prime {divisors : List ℕ} {a len i : ℕ}
    (hd2 : ∀ d ∈ divisors, 2 ≤ d)
    (hcov : ∀ q, Nat.Prime q → q ≤ Nat.sqrt (a + i) → q ∈ divisors)
    (ha : 2 ≤ a) (hi : i < len)
    (hbit : (candidateMask divisors a len).testBit i = true) :
    Nat.Prime (a + i) := by
  by_contra hnp
  have hn2 : 2 ≤ a + i := by omega
  obtain ⟨q, hq, hqdvd, hqle⟩ := exists_prime_le_sqrt hn2 hnp
  exact candidateMask_not_dvd divisors a len q i hd2 (hcov q hq hqle) hi hbit hqdvd

-- ============================================================
-- Bridge from a group mask slice to primality
-- ============================================================

theorem mask_bit_prime {base top a i : ℕ} (hbase : base ≤ a) (hb1 : 1 ≤ base)
    (hsq : top ≤ base * base)
    (h8 : a + 1 + i ≤ 10 ^ 8) (hidx : a - base + i < top - base)
    (hbit : (RosserSieveData.mask base top).testBit (a - base + i) = true) :
    Nat.Prime (a + 1 + i) := by
  have hle_top : a + 1 + i ≤ top := by omega
  have hd2 : ∀ d ∈ smallDivisors base, 2 ≤ d := fun d hd => (smallDivisors_bounds base d hd).1
  have hcov : ∀ q, Nat.Prime q → q ≤ Nat.sqrt (base + 1 + (a - base + i)) →
      q ∈ smallDivisors base := by
    intro q hq hqle
    have hid : base + 1 + (a - base + i) = a + 1 + i := by omega
    rw [hid] at hqle
    have hq10000 : q ≤ 10000 := by
      have hs : Nat.sqrt (a + 1 + i) ≤ 10000 := by
        rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
        norm_num
        omega
      omega
    have hqdiv : q ∈ divisors := divisors_cover q hq hq10000
    have hqbase : q ≤ base := by
      have hs : Nat.sqrt (a + 1 + i) ≤ base := by
        rw [← Nat.lt_succ_iff, Nat.sqrt_lt]
        nlinarith [hsq, hle_top]
      omega
    exact List.mem_filter.mpr ⟨hqdiv, by rw [decide_eq_true_eq]; exact hqbase⟩
  have hbit' : (candidateMask (smallDivisors base) (base + 1) (top - base)).testBit
      (a - base + i) = true := by
    simpa only [RosserSieveData.mask] using hbit
  have hres := candidateMask_bit_prime hd2 hcov (by omega) hidx hbit'
  have heq : base + 1 + (a - base + i) = a + 1 + i := by omega
  rwa [heq] at hres

theorem mask_bit_prime' {base top a i : ℕ} (hbase : base ≤ a)
    (hidx : a - base + i < top - base)
    (hp : Nat.Prime (a + 1 + i)) :
    (RosserSieveData.mask base top).testBit (a - base + i) = true := by
  have hds : ∀ d ∈ smallDivisors base, 2 ≤ d ∧ d < base + 1 := smallDivisors_bounds base
  have hp' : Nat.Prime (base + 1 + (a - base + i)) := by
    have heq : base + 1 + (a - base + i) = a + 1 + i := by omega
    rwa [heq]
  have hres := candidateMask_preserves_prime (smallDivisors base) (base + 1) (top - base)
    (a - base + i) hds hidx hp'
  simpa only [RosserSieveData.mask] using hres

theorem mask_bit_iff {base top a i : ℕ} (hbase : base ≤ a) (hb1 : 1 ≤ base)
    (hsq : top ≤ base * base)
    (h8 : a + 1 + i ≤ 10 ^ 8) (hidx : a - base + i < top - base) :
    (RosserSieveData.mask base top).testBit (a - base + i) = true ↔
      Nat.Prime (a + 1 + i) :=
  ⟨fun hb => mask_bit_prime hbase hb1 hsq h8 hidx hb,
    fun hp => mask_bit_prime' hbase hidx hp⟩

theorem slice_bit {base a b m i : ℕ} (hi : i < b - a) :
    (m / 2 ^ (a - base) % 2 ^ (b - a)).testBit i = m.testBit (a - base + i) := by
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm]
  simp [hi]

theorem candidateCount_slice_eq {base top a b : ℕ}
    (hbase : base ≤ a) (hb1 : 1 ≤ base) (hsq : top ≤ base * base) (hb : b ≤ top)
    (h8 : b ≤ 10 ^ 8) :
    RosserPackedBarrier.candidateCount
        (RosserSieveData.mask base top / 2 ^ (a - base) % 2 ^ (b - a)) (b - a) =
      ((Nat.primesLE b).filter (fun p => a < p)).card := by
  have hpt : ∀ i, i < b - a →
      (RosserSieveData.mask base top / 2 ^ (a - base) % 2 ^ (b - a)).testBit i =
        decide (Nat.Prime (a + 1 + i)) := by
    intro i hi
    by_cases hp : Nat.Prime (a + 1 + i)
    · have hbit : (RosserSieveData.mask base top / 2 ^ (a - base) % 2 ^ (b - a)).testBit i =
          true := by
        rw [slice_bit hi]
        exact (mask_bit_iff hbase hb1 hsq (by omega) (by omega)).mpr hp
      simp [hp, hbit]
    · have hfalse : (RosserSieveData.mask base top / 2 ^ (a - base) % 2 ^ (b - a)).testBit i =
          false := by
        apply Bool.eq_false_iff.mpr
        intro hb2
        rw [slice_bit hi] at hb2
        exact hp ((mask_bit_iff hbase hb1 hsq (by omega) (by omega)).mp hb2)
      simp [hp, hfalse]
  unfold RosserPackedBarrier.candidateCount
  have hfilter : (List.range (b - a)).filter
      (fun i => (RosserSieveData.mask base top / 2 ^ (a - base) % 2 ^ (b - a)).testBit i) =
      (List.range (b - a)).filter (fun i => decide (Nat.Prime (a + 1 + i))) := by
    apply List.filter_congr
    intro i hi
    exact hpt i (List.mem_range.mp hi)
  rw [hfilter]
  have hnodup : ((List.range (b - a)).filter
      (fun i => decide (Nat.Prime (a + 1 + i)))).map (fun i => a + 1 + i) |>.Nodup :=
    List.Nodup.map (fun x y hxy => by omega) (List.nodup_range.filter _)
  have hset : (((List.range (b - a)).filter
      (fun i => decide (Nat.Prime (a + 1 + i)))).map (fun i => a + 1 + i)).toFinset =
      (Nat.primesLE b).filter (fun p => a < p) := by
    ext p
    simp only [List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range,
      decide_eq_true_eq, Nat.mem_primesLE, Finset.mem_filter]
    constructor
    · rintro ⟨i, ⟨hi, hp⟩, heq⟩
      exact ⟨⟨by omega, heq ▸ hp⟩, by omega⟩
    · rintro ⟨⟨hpb, hp⟩, hap⟩
      refine ⟨p - (a + 1), ⟨by omega, ?_⟩, by omega⟩
      have heq : a + 1 + (p - (a + 1)) = p := by omega
      rwa [heq]
  calc ((List.range (b - a)).filter (fun i => decide (Nat.Prime (a + 1 + i)))).length
      = (((List.range (b - a)).filter (fun i => decide (Nat.Prime (a + 1 + i)))).map
          (fun i => a + 1 + i)).length := (List.length_map _).symm
    _ = (((List.range (b - a)).filter
          (fun i => decide (Nat.Prime (a + 1 + i)))).map (fun i => a + 1 + i)).toFinset.card :=
        (List.toFinset_card_of_nodup hnodup).symm
    _ = ((Nat.primesLE b).filter (fun p => a < p)).card := by rw [hset]

end AxlerSieve


