-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Series
-- name    : liuyao_ca_fd889115_k1_Analysis_Series
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:54:15.720105+00:00
-- url     : https://prove2.me/theorems/59860dcb-0123-4a09-836a-2ddc1a3f6a24
-- title:
--   Computable analysis · Series · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableAnalysis/Series.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_Basic
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_PowerSeries

set_option autoImplicit true

/-!
# Iteration-style series constructions

This file starts the lower-level construction layer discussed in the design
notes: a series algorithm is indexed by an iteration count, and it later
compiles to the precision-query `RealCompute` interface.
-/

namespace ComputableAnalysis

namespace Series

/-! ## Elementary finite sums

These definitions are recursion-first finite counterparts of the arithmetic
and geometric series identities.  They use only natural recursion and exact
rational algebra; no infinite-sum or completed-real interface is involved.
-/

def arithmeticSum : Nat -> Rat
  | 0 => 0
  | n + 1 => arithmeticSum n + (n : Rat)

theorem arithmeticSum_succ (n : Nat) :
    arithmeticSum (n + 1) = arithmeticSum n + (n : Rat) := by
  rfl

theorem arithmeticSum_eq (n : Nat) :
    arithmeticSum n = (n : Rat) * ((n : Rat) - 1) / 2 := by
  induction n with
  | zero =>
      simp [arithmeticSum, Rat.div_def]
  | succ n ih =>
      rw [arithmeticSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

def arithmeticProgressionSum (a d : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => arithmeticProgressionSum a d n + (a + (n : Rat) * d)

theorem arithmeticProgressionSum_succ (a d : Rat) (n : Nat) :
    arithmeticProgressionSum a d (n + 1) =
      arithmeticProgressionSum a d n + (a + (n : Rat) * d) := by
  rfl

theorem arithmeticProgressionSum_eq (a d : Rat) (n : Nat) :
    arithmeticProgressionSum a d n =
      (n : Rat) * (2 * a + ((n : Rat) - 1) * d) / 2 := by
  induction n with
  | zero =>
      simp [arithmeticProgressionSum, Rat.div_def]
  | succ n ih =>
      rw [arithmeticProgressionSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem arithmeticProgressionSum_constant (a : Rat) (n : Nat) :
    arithmeticProgressionSum a 0 n = (n : Rat) * a := by
  induction n with
  | zero => simp [arithmeticProgressionSum]
  | succ n ih =>
      rw [arithmeticProgressionSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.add_mul, Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]

theorem arithmeticProgressionSum_le_succ {a d : Rat}
    (ha : 0 <= a) (hd : 0 <= d) (n : Nat) :
    arithmeticProgressionSum a d n <= arithmeticProgressionSum a d (n + 1) := by
  rw [arithmeticProgressionSum_succ]
  have hterm : 0 <= a + (n : Rat) * d := by
    exact Rat.add_nonneg ha (Rat.mul_nonneg Rat.natCast_nonneg hd)
  have hadd : arithmeticProgressionSum a d n + 0 <=
      arithmeticProgressionSum a d n + (a + (n : Rat) * d) :=
    (Rat.add_le_add_left).2 hterm
  grind

theorem arithmeticProgressionSum_le_of_le {a d : Rat}
    (ha : 0 <= a) (hd : 0 <= d) {n m : Nat} (hnm : n <= m) :
    arithmeticProgressionSum a d n <=
      arithmeticProgressionSum a d m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (arithmeticProgressionSum_le_succ ha hd _)

theorem arithmeticProgressionSum_nonneg {a d : Rat}
    (ha : 0 <= a) (hd : 0 <= d) (n : Nat) :
    0 <= arithmeticProgressionSum a d n := by
  induction n with
  | zero => simp [arithmeticProgressionSum]
  | succ n ih =>
      rw [arithmeticProgressionSum_succ]
      exact Rat.add_nonneg ih
        (Rat.add_nonneg ha (Rat.mul_nonneg Rat.natCast_nonneg hd))

theorem arithmeticProgressionSum_pos {a d : Rat}
    (ha : 0 < a) (hd : 0 <= d) {n : Nat} (hn : 0 < n) :
    0 < arithmeticProgressionSum a d n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [arithmeticProgressionSum_succ]
      cases n with
      | zero =>
          simp [arithmeticProgressionSum]
          grind
      | succ n =>
          have hsum : 0 < arithmeticProgressionSum a d (n + 1) :=
            ih (by omega)
          have hterm : 0 <= a + ((n + 1 : Nat) : Rat) * d := by
            exact Rat.add_nonneg (Rat.le_of_lt ha)
              (Rat.mul_nonneg Rat.natCast_nonneg hd)
          grind

theorem arithmeticSum_nonneg (n : Nat) : 0 <= arithmeticSum n := by
  induction n with
  | zero => simp [arithmeticSum]
  | succ n ih =>
      rw [arithmeticSum_succ]
      exact Rat.add_nonneg ih Rat.natCast_nonneg

theorem arithmeticSum_pos {n : Nat} (hn : 1 < n) :
    0 < arithmeticSum n := by
  rw [arithmeticSum_eq, Rat.div_def]
  have hn0 : 0 < n := by omega
  have hnr : 0 < (n : Rat) := by exact_mod_cast hn0
  have hdiff : 0 < (n : Rat) - 1 := by
    have hnr_one : (1 : Rat) < (n : Rat) := by exact_mod_cast hn
    grind
  have hinv : 0 < (2 : Rat)⁻¹ := (Rat.inv_pos).2 (by decide +kernel)
  exact Rat.mul_pos (Rat.mul_pos hnr hdiff) hinv

theorem arithmeticSum_le_succ (n : Nat) :
    arithmeticSum n <= arithmeticSum (n + 1) := by
  rw [arithmeticSum_succ]
  have h : arithmeticSum n + 0 <= arithmeticSum n + (n : Rat) :=
    (Rat.add_le_add_left).2 Rat.natCast_nonneg
  grind

theorem arithmeticSum_le_of_le {n m : Nat} (hnm : n <= m) :
    arithmeticSum n <= arithmeticSum m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (arithmeticSum_le_succ _)

theorem arithmeticSum_reaches (target : Nat) :
    (target : Rat) <= arithmeticSum (2 * target + 1) := by
  rw [arithmeticSum_eq]
  simp only [Rat.natCast_add, Rat.natCast_mul]
  have htwo : ((2 : Nat) : Rat) = 2 := by decide +kernel
  have hone : ((1 : Nat) : Rat) = 1 := by decide +kernel
  rw [htwo, hone]
  have hsub : 2 * (target : Rat) + 1 - 1 = 2 * (target : Rat) := by
    grind
  rw [hsub, Rat.div_def]
  have hhalf : 2 * (target : Rat) * (2 : Rat)⁻¹ = target := by
    grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  have hnonneg : 0 <= (target : Rat) := Rat.natCast_nonneg
  have hfactor : (1 : Rat) <= 2 * (target : Rat) + 1 := by grind
  calc
    (target : Rat) <= (target : Rat) * (2 * (target : Rat) + 1) := by
      simpa only [Rat.mul_one] using
        (Rat.mul_le_mul_of_nonneg_left hfactor hnonneg)
    _ = (2 * (target : Rat) + 1) *
        (2 * (target : Rat) * (2 : Rat)⁻¹) := by
      rw [hhalf]
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (2 * (target : Rat) + 1) * (2 * (target : Rat)) *
        (2 : Rat)⁻¹ := by
      grind [Rat.mul_assoc]

theorem arithmeticSum_reaches_later
    (target n : Nat) (hstage : 2 * target + 1 <= n) :
    (target : Rat) <= arithmeticSum n := by
  exact Rat.le_trans (arithmeticSum_reaches target)
    (arithmeticSum_le_of_le hstage)

/-! A reusable finite power-sum evaluator.  The closed forms below are kept
for the low powers where they are useful, while this recurrence handles every
fixed exponent without introducing a general Bernoulli-number layer. -/

def powerSum (k : Nat) : Nat -> Rat
  | 0 => 0
  | n + 1 => powerSum k n + (n : Rat) ^ k

theorem powerSum_zero (k : Nat) : powerSum k 0 = 0 := by
  rfl

theorem powerSum_succ (k n : Nat) :
    powerSum k (n + 1) = powerSum k n + (n : Rat) ^ k := by
  rfl

/-! A finite shifted block evaluator exposes the terms appended when a
power-sum prefix is extended.  It is deliberately recursive in the block
length, so it supplies transport data for staged computations without a
Faulhaber formula or any convergence assertion. -/

def powerSumBlock (k n : Nat) : Nat -> Rat
  | 0 => 0
  | m + 1 => powerSumBlock k n m + ((n + m : Nat) : Rat) ^ k

theorem powerSumBlock_succ (k n m : Nat) :
    powerSumBlock k n (m + 1) =
      powerSumBlock k n m + ((n + m : Nat) : Rat) ^ k := by
  rfl

theorem powerSum_add_block (k n m : Nat) :
    powerSum k (n + m) = powerSum k n + powerSumBlock k n m := by
  induction m with
  | zero =>
      simp [powerSumBlock]
      grind
  | succ m ih =>
      rw [show n + (m + 1) = (n + m) + 1 by omega]
      rw [powerSum_succ, ih, powerSumBlock_succ]
      grind [Rat.add_assoc]

theorem powerSum_nonneg (k n : Nat) : 0 <= powerSum k n := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
      rw [powerSum_succ]
      exact Rat.add_nonneg ih (Rat.pow_nonneg Rat.natCast_nonneg)

theorem powerSum_le_succ (k n : Nat) :
    powerSum k n <= powerSum k (n + 1) := by
  rw [powerSum_succ]
  have h := (Rat.add_le_add_left
    (a := (0 : Rat))
    (b := (n : Rat) ^ k)
    (c := powerSum k n)).2
    (Rat.pow_nonneg Rat.natCast_nonneg)
  simpa only [Rat.add_zero] using h

theorem powerSum_le_of_le (k : Nat) {n m : Nat} (hnm : n <= m) :
    powerSum k n <= powerSum k m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (powerSum_le_succ k _)

/-- Every finite power-sum prefix has an explicit polynomial growth bound.

The evaluator sums the terms with indices below `n`; each term is bounded by
`n^k`, so the prefix is bounded by `n * n^k`.  This is a finite rational
certificate useful when a later construction treats the index as a potential
infinity parameter. -/
theorem powerSum_le_mul_pow (k n : Nat) :
    powerSum k n <= (n : Rat) * (n : Rat) ^ k := by
  have pow_mono : ∀ j m : Nat,
      (m : Rat) ^ j <= ((m + 1 : Nat) : Rat) ^ j := by
    intro j m
    induction j with
    | zero => simp
    | succ j ih =>
        rw [Rat.pow_succ, Rat.pow_succ]
        have hleft : (m : Rat) ^ j * (m : Rat) <=
            ((m + 1 : Nat) : Rat) ^ j * (m : Rat) :=
          Rat.mul_le_mul_of_nonneg_right ih Rat.natCast_nonneg
        have hright : ((m + 1 : Nat) : Rat) ^ j * (m : Rat) <=
            ((m + 1 : Nat) : Rat) ^ j * ((m + 1 : Nat) : Rat) := by
          apply Rat.mul_le_mul_of_nonneg_left
          · simp only [Rat.natCast_add]
            grind
          · exact Rat.pow_nonneg Rat.natCast_nonneg
        exact Rat.le_trans hleft hright
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
      rw [powerSum_succ]
      have hpow : (n : Rat) ^ k <= ((n + 1 : Nat) : Rat) ^ k :=
        pow_mono k n
      have hterm : (n : Rat) ^ k <=
          ((n + 1 : Nat) : Rat) ^ k := hpow
      have hscaled : (n : Rat) * (n : Rat) ^ k + (n : Rat) ^ k <=
          ((n + 1 : Nat) : Rat) * ((n + 1 : Nat) : Rat) ^ k := by
        have hprefix : (n : Rat) * (n : Rat) ^ k + (n : Rat) ^ k <=
            (n : Rat) * ((n + 1 : Nat) : Rat) ^ k +
              ((n + 1 : Nat) : Rat) ^ k := by
          have hmul := Rat.mul_le_mul_of_nonneg_left hpow
            (Rat.natCast_nonneg : (0 : Rat) <= (n : Rat))
          calc
            (n : Rat) * (n : Rat) ^ k + (n : Rat) ^ k <=
                (n : Rat) * ((n + 1 : Nat) : Rat) ^ k + (n : Rat) ^ k :=
              (Rat.add_le_add_right).2 hmul
            _ <= (n : Rat) * ((n + 1 : Nat) : Rat) ^ k +
                ((n + 1 : Nat) : Rat) ^ k :=
              (Rat.add_le_add_left).2 hterm
        simp only [Rat.natCast_add] at hprefix ⊢
        grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]
      exact Rat.le_trans ((Rat.add_le_add_right).2 ih) hscaled

theorem rat_one_pow (k : Nat) : (1 : Rat) ^ k = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Rat.pow_succ, ih]
      simp

theorem rat_zero_pow_of_pos {k : Nat} (hk : 0 < k) :
    (0 : Rat) ^ k = 0 := by
  cases k with
  | zero => omega
  | succ k =>
      rw [Rat.pow_succ]
      simp

theorem powerSum_pos {k : Nat} (hk : 0 < k) {n : Nat}
    (hn : 1 < n) : 0 < powerSum k n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [powerSum_succ]
      cases n with
      | zero => omega
      | succ n =>
          cases n with
          | zero =>
              have hzero := rat_zero_pow_of_pos hk
              have hone := rat_one_pow k
              simp [powerSum, hzero, hone]
              decide +kernel
          | succ n =>
              have hsum : 0 < powerSum k (n + 2) := by
                apply ih
                omega
              have hterm : 0 <= ((n + 2 : Nat) : Rat) ^ k :=
                Rat.pow_nonneg Rat.natCast_nonneg
              grind

theorem powerSum_zero_exponent (n : Nat) :
    powerSum 0 n = (n : Rat) := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
      rw [powerSum_succ, ih]
      simp only [Rat.pow_zero, Rat.natCast_add]
      grind

theorem powerSum_one_exponent (n : Nat) :
    powerSum 1 n = arithmeticSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, arithmeticSum_succ]
      simp

def squareSum : Nat -> Rat
  | 0 => 0
  | n + 1 => squareSum n + (n : Rat) ^ 2

theorem squareSum_succ (n : Nat) :
    squareSum (n + 1) = squareSum n + (n : Rat) ^ 2 := by
  rfl

theorem squareSum_eq (n : Nat) :
    squareSum n = (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) / 6 := by
  induction n with
  | zero =>
      simp [squareSum, Rat.div_def]
  | succ n ih =>
      rw [squareSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def cubeSum : Nat -> Rat
  | 0 => 0
  | n + 1 => cubeSum n + (n : Rat) ^ 3

theorem cubeSum_succ (n : Nat) :
    cubeSum (n + 1) = cubeSum n + (n : Rat) ^ 3 := by
  rfl

theorem cubeSum_eq (n : Nat) :
    cubeSum n = (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 / 4 := by
  induction n with
  | zero =>
      decide +kernel
  | succ n ih =>
      rw [cubeSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def fourthPowerSum : Nat -> Rat
  | 0 => 0
  | n + 1 => fourthPowerSum n + (n : Rat) ^ 4

theorem fourthPowerSum_succ (n : Nat) :
    fourthPowerSum (n + 1) = fourthPowerSum n + (n : Rat) ^ 4 := by
  rfl

theorem fourthPowerSum_eq (n : Nat) :
    fourthPowerSum n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) / 30 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [fourthPowerSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def fifthPowerSum : Nat -> Rat
  | 0 => 0
  | n + 1 => fifthPowerSum n + (n : Rat) ^ 5

theorem fifthPowerSum_succ (n : Nat) :
    fifthPowerSum (n + 1) = fifthPowerSum n + (n : Rat) ^ 5 := by
  rfl

theorem fifthPowerSum_eq (n : Nat) :
    fifthPowerSum n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (2 * (n : Rat) ^ 2 - 2 * (n : Rat) - 1) / 12 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [fifthPowerSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def sixthPowerSum : Nat -> Rat
  | 0 => 0
  | n + 1 => sixthPowerSum n + (n : Rat) ^ 6

theorem sixthPowerSum_succ (n : Nat) :
    sixthPowerSum (n + 1) = sixthPowerSum n + (n : Rat) ^ 6 := by
  rfl

theorem sixthPowerSum_eq (n : Nat) :
    sixthPowerSum n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 + 3 * (n : Rat) + 1) / 42 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [sixthPowerSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def seventhPowerSum : Nat -> Rat
  | 0 => 0
  | n + 1 => seventhPowerSum n + (n : Rat) ^ 7

theorem seventhPowerSum_succ (n : Nat) :
    seventhPowerSum (n + 1) = seventhPowerSum n + (n : Rat) ^ 7 := by
  rfl

theorem seventhPowerSum_eq (n : Nat) :
    seventhPowerSum n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 - (n : Rat) ^ 2 +
          4 * (n : Rat) + 2) / 24 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [seventhPowerSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

def eighthPowerSum : Nat -> Rat
  | 0 => 0
  | n + 1 => eighthPowerSum n + (n : Rat) ^ 8

theorem eighthPowerSum_succ (n : Nat) :
    eighthPowerSum (n + 1) = eighthPowerSum n + (n : Rat) ^ 8 := by
  rfl

theorem eighthPowerSum_eq (n : Nat) :
    eighthPowerSum n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (5 * (n : Rat) ^ 6 - 15 * (n : Rat) ^ 5 +
          5 * (n : Rat) ^ 4 + 15 * (n : Rat) ^ 3 -
          (n : Rat) ^ 2 - 9 * (n : Rat) - 3) / 90 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [eighthPowerSum_succ, ih]
      simp only [Rat.natCast_add]
      grind [Rat.div_def, Rat.sub_eq_add_neg, Rat.mul_add,
        Rat.add_mul, Rat.mul_assoc, Rat.mul_comm, Rat.pow_succ]

theorem powerSum_two_exponent (n : Nat) :
    powerSum 2 n = squareSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, squareSum_succ]

theorem powerSum_three_exponent (n : Nat) :
    powerSum 3 n = cubeSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, cubeSum_succ]

/-! These bridges expose the closed rational formulas through the generic
power-sum evaluator.  They are finite identities: `n` is an iteration
count, so no infinite sum or completed value is introduced. -/

theorem powerSum_two_closed_form (n : Nat) :
    powerSum 2 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) / 6 := by
  rw [powerSum_two_exponent, squareSum_eq]

theorem powerSum_three_closed_form (n : Nat) :
    powerSum 3 n = (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 / 4 := by
  rw [powerSum_three_exponent, cubeSum_eq]

theorem powerSum_four_exponent (n : Nat) :
    powerSum 4 n = fourthPowerSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, fourthPowerSum_succ]

theorem powerSum_four_closed_form (n : Nat) :
    powerSum 4 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 2 - 3 * (n : Rat) - 1) / 30 := by
  rw [powerSum_four_exponent, fourthPowerSum_eq]

theorem powerSum_five_exponent (n : Nat) :
    powerSum 5 n = fifthPowerSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, fifthPowerSum_succ]

theorem powerSum_six_exponent (n : Nat) :
    powerSum 6 n = sixthPowerSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, sixthPowerSum_succ]

theorem powerSum_seven_exponent (n : Nat) :
    powerSum 7 n = seventhPowerSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, seventhPowerSum_succ]

theorem powerSum_eight_exponent (n : Nat) :
    powerSum 8 n = eighthPowerSum n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [powerSum_succ, ih, eighthPowerSum_succ]

theorem powerSum_five_closed_form (n : Nat) :
    powerSum 5 n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (2 * (n : Rat) ^ 2 - 2 * (n : Rat) - 1) / 12 := by
  rw [powerSum_five_exponent, fifthPowerSum_eq]

theorem powerSum_six_closed_form (n : Nat) :
    powerSum 6 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 + 3 * (n : Rat) + 1) / 42 := by
  rw [powerSum_six_exponent, sixthPowerSum_eq]

theorem powerSum_seven_closed_form (n : Nat) :
    powerSum 7 n =
      (n : Rat) ^ 2 * ((n : Rat) - 1) ^ 2 *
        (3 * (n : Rat) ^ 4 - 6 * (n : Rat) ^ 3 - (n : Rat) ^ 2 +
          4 * (n : Rat) + 2) / 24 := by
  rw [powerSum_seven_exponent, seventhPowerSum_eq]

theorem powerSum_eight_finite_bridge (n : Nat) :
    powerSum 8 n =
      eighthPowerSum n := by
  rw [powerSum_eight_exponent]

theorem powerSum_eight_closed_form (n : Nat) :
    powerSum 8 n =
      (n : Rat) * ((n : Rat) - 1) * (2 * (n : Rat) - 1) *
        (5 * (n : Rat) ^ 6 - 15 * (n : Rat) ^ 5 +
          5 * (n : Rat) ^ 4 + 15 * (n : Rat) ^ 3 -
          (n : Rat) ^ 2 - 9 * (n : Rat) - 3) / 90 := by
  rw [powerSum_eight_finite_bridge, eighthPowerSum_eq]

def geometricSum (r : Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => geometricSum r n + r ^ n

theorem geometricSum_succ (r : Rat) (n : Nat) :
    geometricSum r (n + 1) = geometricSum r n + r ^ n := by
  rfl

/-! A later finite geometric prefix can be transported from an earlier
prefix by exposing the shifted block.  This is a finite recurrence for staged
algorithms; it does not refer to an infinite sum or a completed limit. -/
theorem geometricSum_add_block (r : Rat) (n m : Nat) :
    geometricSum r (n + m) =
      geometricSum r n + r ^ n * geometricSum r m := by
  induction m with
  | zero =>
      simp [geometricSum]
      grind
  | succ m ih =>
      rw [Nat.add_succ, geometricSum_succ, ih, geometricSum_succ]
      have hpow : ∀ j : Nat, r ^ (n + j) = r ^ n * r ^ j := by
        intro j
        induction j with
        | zero => simp
        | succ j ihj =>
            rw [Nat.add_succ, Rat.pow_succ, Rat.pow_succ, ihj]
            grind [Rat.mul_assoc, Rat.mul_comm]
      rw [hpow m]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc]

theorem geometricSum_zero (r : Rat) : geometricSum r 0 = 0 := by
  rfl

theorem geometricSum_nonneg {r : Rat} (hr : 0 <= r) (n : Nat) :
    0 <= geometricSum r n := by
  induction n with
  | zero => simp [geometricSum]
  | succ n ih =>
      rw [geometricSum_succ]
      exact Rat.add_nonneg ih (Rat.pow_nonneg hr)

theorem geometricSum_le_succ {r : Rat} (hr : 0 <= r) (n : Nat) :
    geometricSum r n <= geometricSum r (n + 1) := by
  rw [geometricSum_succ]
  have hp : 0 <= r ^ n := Rat.pow_nonneg hr
  grind

theorem geometricSum_pos {r : Rat} (hr : 0 < r) {n : Nat}
    (hn : 0 < n) : 0 < geometricSum r n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [geometricSum_succ]
      cases n with
      | zero =>
          simp [geometricSum]
          decide +kernel
      | succ n =>
          have hsum : 0 < geometricSum r (n + 1) := ih (by omega)
          have hterm : 0 < r ^ (n + 1) := Rat.pow_pos hr
          grind

theorem geometricSum_one (n : Nat) : geometricSum 1 n = (n : Rat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [geometricSum_succ, ih]
      have hone : ∀ k : Nat, (1 : Rat) ^ k = 1 := by
        intro k
        induction k with
        | zero => simp [Rat.pow_zero]
        | succ n ih => rw [Rat.pow_succ, ih]; simp
      rw [hone n]
      simp [Rat.natCast_add]

theorem geometricSum_zero_ratio {n : Nat} (hn : 0 < n) :
    geometricSum 0 n = 1 := by
  induction n with
  | zero => omega
  | succ n ih =>
      rw [geometricSum_succ]
      cases n with
      | zero => simp [geometricSum] <;> grind
      | succ n =>
          have hpos : 0 < n + 1 := by omega
          have hih := ih hpos
          rw [hih]
          have hpow : 0 < n + 1 := by omega
          simp [Rat.pow_succ] <;> grind

theorem geometricSum_mul_sub (r : Rat) (n : Nat) :
    (r - 1) * geometricSum r n = r ^ n - 1 := by
  induction n with
  | zero => grind [geometricSum, Rat.sub_eq_add_neg]
  | succ n ih =>
      rw [geometricSum_succ]
      rw [Rat.mul_add, ih, Rat.pow_succ]
      grind [Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

theorem geometricSum_tail_eq (r : Rat) (n : Nat) :
    1 - (1 - r) * geometricSum r n = r ^ n := by
  have h := geometricSum_mul_sub r n
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
    Rat.add_assoc, Rat.add_comm, Rat.mul_assoc, Rat.mul_comm]

theorem geometricSum_le_inv_one_sub {r : Rat}
    (hr0 : 0 <= r) (hr1 : r < 1) (n : Nat) :
    geometricSum r n <= 1 / (1 - r) := by
  have hden : 0 < (1 : Rat) - r := by grind
  have hpow : 0 <= r ^ n := Rat.pow_nonneg hr0
  have hprod : geometricSum r n * (1 - r) <= 1 := by
    have htail := geometricSum_tail_eq r n
    grind [Rat.mul_comm]
  apply Rat.le_of_mul_le_mul_right (c := (1 : Rat) - r)
  · calc
      geometricSum r n * (1 - r) <= 1 := hprod
      _ = (1 / (1 - r)) * (1 - r) := by
        rw [Rat.div_def]
        have hcancel : (1 - r)⁻¹ * (1 - r) = 1 :=
          Rat.inv_mul_cancel (1 - r) (Rat.ne_of_gt hden)
        grind [Rat.mul_assoc, Rat.mul_comm]
  · exact hden

theorem geometricSum_tail_nonneg {r : Rat}
    (hr0 : 0 <= r) (n : Nat) :
    0 <= 1 - (1 - r) * geometricSum r n := by
  rw [geometricSum_tail_eq]
  exact Rat.pow_nonneg hr0

theorem geometricSum_tail_pos {r : Rat}
    (hr : 0 < r) (n : Nat) :
    0 < 1 - (1 - r) * geometricSum r n := by
  rw [geometricSum_tail_eq]
  exact Rat.pow_pos hr

theorem geometricSum_tail_le_one {r : Rat}
    (hr0 : 0 <= r) (hr1 : r <= 1) (n : Nat) :
    1 - (1 - r) * geometricSum r n <= 1 := by
  rw [geometricSum_tail_eq]
  have hpow : r ^ n <= 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Rat.pow_succ]
        calc
          r ^ n * r <= 1 * r :=
            Rat.mul_le_mul_of_nonneg_right ih hr0
          _ <= 1 * 1 :=
            Rat.mul_le_mul_of_nonneg_left hr1 (by decide +kernel)
          _ = 1 := by decide +kernel
  exact hpow

theorem geometricSum_tail_lt_one {r : Rat}
    (hr0 : 0 <= r) (hr1 : r < 1) {n : Nat} (hn : 0 < n) :
    1 - (1 - r) * geometricSum r n < 1 := by
  rw [geometricSum_tail_eq]
  have hpow : r ^ n < 1 := by
    induction n with
    | zero => omega
    | succ n ih =>
        rw [Rat.pow_succ]
        have hpow_le : r ^ n <= 1 := by
          by_cases hnzero : n = 0
          · subst n
            simp
          · exact Rat.le_of_lt (ih (Nat.pos_of_ne_zero hnzero))
        have hmul_le : r ^ n * r <= 1 * r :=
          Rat.mul_le_mul_of_nonneg_right hpow_le hr0
        have hmul_lt : 1 * r < 1 * 1 :=
          Rat.mul_lt_mul_of_pos_left hr1 (by decide +kernel)
        have hmul : r ^ n * r < 1 * 1 := by grind
        grind
  exact hpow

theorem half_pow_eq_one_div_nat_two_pow (n : Nat) :
    ((1 : Rat) / 2) ^ n = 1 / (((2 ^ n : Nat) : Rat)) := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
      rw [Rat.pow_succ, ih, Nat.pow_succ, Rat.natCast_mul]
      rw [Rat.div_def, Rat.div_def, Rat.div_def, Rat.one_mul]
      grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]

theorem half_pow_le_one_div_succ (n : Nat) :
    ((1 : Rat) / 2) ^ n <= 1 / ((n + 1 : Nat) : Rat) := by
  have hnat : n + 1 <= 2 ^ n := by
    induction n with
    | zero => omega
    | succ n ih =>
        calc
          n + 1 + 1 <= 2 * (n + 1) := by omega
          _ <= 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
          _ = 2 ^ (n + 1) := by rw [Nat.pow_succ]; omega
  have hcast : ((n + 1 : Nat) : Rat) <= ((2 ^ n : Nat) : Rat) := by
    exact_mod_cast hnat
  have hleft : 0 < ((n + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.succ_pos n)
  have hright : 0 < ((2 ^ n : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (Nat.pow_pos (by omega : 0 < 2))
  have hinv : 1 / ((2 ^ n : Nat) : Rat) <=
      1 / ((n + 1 : Nat) : Rat) := by
    apply Rat.le_of_mul_le_mul_right
      (c := ((n + 1 : Nat) : Rat) * ((2 ^ n : Nat) : Rat))
    · rw [Rat.div_def, Rat.div_def]
      have hleft_ne : ((n + 1 : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hleft
      have hright_ne : ((2 ^ n : Nat) : Rat) ≠ 0 := Rat.ne_of_gt hright
      have hleft_eq :
          ((2 ^ n : Nat) : Rat)⁻¹ *
              (((n + 1 : Nat) : Rat) * ((2 ^ n : Nat) : Rat)) =
            ((n + 1 : Nat) : Rat) := by
        have hcancel := Rat.inv_mul_cancel ((2 ^ n : Nat) : Rat) hright_ne
        grind [Rat.mul_assoc, Rat.mul_comm]
      have hright_eq :
          ((n + 1 : Nat) : Rat)⁻¹ *
              (((n + 1 : Nat) : Rat) * ((2 ^ n : Nat) : Rat)) =
            ((2 ^ n : Nat) : Rat) := by
        have hcancel := Rat.inv_mul_cancel ((n + 1 : Nat) : Rat) hleft_ne
        grind [Rat.mul_assoc, Rat.mul_comm]
      simp only [Rat.one_mul]
      rw [hleft_eq, hright_eq]
      exact hcast
    · exact Rat.mul_pos hleft hright
  have hpow := half_pow_eq_one_div_nat_two_pow n
  rw [hpow]
  exact hinv

theorem geometricSum_half_tail_le_one_div_succ (n : Nat) :
    1 - (1 - (1 : Rat) / 2) * geometricSum ((1 : Rat) / 2) n <=
      1 / ((n + 1 : Nat) : Rat) := by
  rw [geometricSum_tail_eq]
  exact half_pow_le_one_div_succ n

theorem pow_le_half_pow {r : Rat} (hr0 : 0 <= r)
    (hrhalf : r <= (1 : Rat) / 2) (n : Nat) :
    r ^ n <= ((1 : Rat) / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ, Rat.pow_succ]
      have hleft : r ^ n * r <= ((1 : Rat) / 2) ^ n * r :=
        Rat.mul_le_mul_of_nonneg_right ih hr0
      have hright : ((1 : Rat) / 2) ^ n * r <=
          ((1 : Rat) / 2) ^ n * ((1 : Rat) / 2) :=
        Rat.mul_le_mul_of_nonneg_left hrhalf
          (Rat.pow_nonneg (by decide +kernel))
      grind

theorem geometricSum_tail_le_one_div_succ_of_le_half
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (n : Nat) :
    1 - (1 - r) * geometricSum r n <=
      1 / ((n + 1 : Nat) : Rat) := by
  rw [geometricSum_tail_eq]
  exact Rat.le_trans (pow_le_half_pow hr0 hrhalf n)
    (half_pow_le_one_div_succ n)

def geometricRaw (r : Rat) (hr0 : 0 <= r) (hr1 : r < 1) : RealCompute where
  compute := fun n =>
    { lo := geometricSum r n, hi := 1 / (1 - r) }

theorem geometricRaw_compute_eq (r : Rat) (hr0 : 0 <= r) (hr1 : r < 1) (n : Nat) :
    (geometricRaw r hr0 hr1).compute n =
      { lo := geometricSum r n, hi := 1 / (1 - r) } := by
  rfl

theorem geometricRaw_valid_of_le_half
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2) (hr1 : r < 1) :
    (geometricRaw r hr0 hr1).Valid := by
  have hden : 0 < 1 - r := by grind
  have hsum_le (n : Nat) :
      geometricSum r n <= 1 / (1 - r) :=
    geometricSum_le_inv_one_sub hr0 hr1 n
  have hmono : forall {n m : Nat}, n <= m ->
      geometricSum r n <= geometricSum r m := by
    intro n m hnm
    induction hnm with
    | refl => exact Rat.le_refl
    | @step m hnm ih =>
        exact Rat.le_trans ih (geometricSum_le_succ hr0 m)
  have hfactor : 1 / (1 - r) <= 2 := by
    apply Rat.le_of_mul_le_mul_right (c := 1 - r)
    · calc
        1 / (1 - r) * (1 - r) = 1 := by
          rw [Rat.div_def, Rat.one_mul,
            Rat.inv_mul_cancel (1 - r) (Rat.ne_of_gt hden)]
        _ <= 2 * (1 - r) := by grind
    · exact hden
  have hbound : forall n : Nat,
      ((geometricRaw r hr0 hr1).compute n).width <=
        (2 : Rat) / ((n + 1 : Nat) : Rat) := by
    intro n
    change 1 / (1 - r) - geometricSum r n <=
      (2 : Rat) / ((n + 1 : Nat) : Rat)
    have hpow := pow_le_half_pow hr0 hrhalf n
    have hhalf := half_pow_le_one_div_succ n
    have hpow' := Rat.le_trans hpow hhalf
    have hinvnonneg : 0 <= (1 - r)⁻¹ :=
      Rat.le_of_lt ((Rat.inv_pos).2 hden)
    have hprod := Rat.mul_le_mul_of_nonneg_right hpow' hinvnonneg
    calc
      1 / (1 - r) - geometricSum r n = r ^ n * (1 - r)⁻¹ := by
        rw [Rat.div_def]
        grind [geometricSum_tail_eq r n, Rat.mul_assoc, Rat.mul_comm]
      _ <= (1 / ((n + 1 : Nat) : Rat)) * 2 := by
        have hinvle : (1 - r)⁻¹ <= 2 := by
          simpa [Rat.div_def, Rat.one_mul] using hfactor
        have hnonneg : 0 <= 1 / ((n + 1 : Nat) : Rat) := by
          exact Rat.le_of_lt (one_div_nat_pos (Nat.zero_lt_succ n))
        exact Rat.le_trans hprod (Rat.mul_le_mul_of_nonneg_left hinvle hnonneg)
      _ = (2 : Rat) / ((n + 1 : Nat) : Rat) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <= 1 / (1 - r) - geometricSum r n
    grind [hsum_le n]
  · intro n m hnm
    change geometricSum r n <= geometricSum r m /\
        geometricSum r m <= 1 / (1 - r) /\
        1 / (1 - r) <= 1 / (1 - r)
    exact ⟨hmono hnm, hsum_le m, Rat.le_refl⟩
  · exact shrinksToZero_of_natOverSuccBound hbound

theorem geometricRaw_equiv_inv_one_sub
    {r : Rat} (hr0 : 0 <= r) (hr1 : r < 1) :
    (geometricRaw r hr0 hr1).Equiv
      (RealCompute.ofRat (1 / (1 - r))) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff
    (geometricRaw r hr0 hr1)
    (RealCompute.ofRat (1 / (1 - r))) n n).2
  constructor
  · exact geometricSum_le_inv_one_sub hr0 hr1 n
  · exact Rat.le_refl

/-! The valid raw geometric representation exposes its finite stage selector
as a public algorithmic theorem. -/
theorem geometricRaw_reaches_of_positive_tolerance
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (eps : QPos) :
    ∃ n : Nat, ((geometricRaw r hr0 hr1).compute n).width <= eps.val := by
  rcases (geometricRaw_valid_of_le_half hr0 hrhalf hr1).2.2 eps with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

def geometricHalfRaw : RealCompute where
  compute := fun n =>
    { lo := geometricSum ((1 : Rat) / 2) n, hi := 2 }

theorem geometricHalfRaw_compute_eq (n : Nat) :
    geometricHalfRaw.compute n =
      { lo := geometricSum ((1 : Rat) / 2) n, hi := 2 } := by
  rfl

theorem geometricHalfRaw_valid : geometricHalfRaw.Valid := by
  have hratio0 : 0 <= (1 : Rat) / 2 := by decide +kernel
  have hratio1 : (1 : Rat) / 2 < 1 := by decide +kernel
  have hsum_le_two (n : Nat) :
      geometricSum ((1 : Rat) / 2) n <= 2 := by
    have h := geometricSum_le_inv_one_sub hratio0 hratio1 n
    have hden : (1 : Rat) / (1 - (1 : Rat) / 2) = 2 := by
      decide +kernel
    rw [hden] at h
    exact h
  have hmono : forall {n m : Nat}, n <= m ->
      geometricSum ((1 : Rat) / 2) n <=
        geometricSum ((1 : Rat) / 2) m := by
    intro n m hnm
    induction hnm with
    | refl => exact Rat.le_refl
    | @step m hnm ih =>
        exact Rat.le_trans ih (geometricSum_le_succ hratio0 m)
  have hbound : forall n : Nat,
      (geometricHalfRaw.compute n).width <=
        (2 : Rat) / ((n + 1 : Nat) : Rat) := by
    intro n
    change 2 - geometricSum ((1 : Rat) / 2) n <=
      (2 : Rat) / ((n + 1 : Nat) : Rat)
    have htail := geometricSum_tail_eq ((1 : Rat) / 2) n
    have hp := half_pow_le_one_div_succ n
    calc
      2 - geometricSum ((1 : Rat) / 2) n =
          2 * (((1 : Rat) / 2) ^ n) := by
            grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.add_mul,
              Rat.mul_assoc, Rat.mul_comm]
      _ <= 2 * (1 / ((n + 1 : Nat) : Rat)) := by
        exact Rat.mul_le_mul_of_nonneg_left hp (by decide +kernel)
      _ = (2 : Rat) / ((n + 1 : Nat) : Rat) := by
        rw [Rat.div_def]
        grind [Rat.mul_assoc, Rat.mul_comm]
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <= 2 - geometricSum ((1 : Rat) / 2) n
    grind [hsum_le_two n]
  · intro n m hnm
    change geometricSum ((1 : Rat) / 2) n <=
        geometricSum ((1 : Rat) / 2) m /\
      geometricSum ((1 : Rat) / 2) m <= 2 /\
      (2 : Rat) <= 2
    exact ⟨hmono hnm, hsum_le_two m, Rat.le_refl⟩
  · exact shrinksToZero_of_natOverSuccBound hbound

theorem geometricHalfRaw_equiv_two :
    geometricHalfRaw.Equiv (RealCompute.ofRat 2) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff geometricHalfRaw (RealCompute.ofRat 2)
    n n).2
  constructor
  · change geometricSum ((1 : Rat) / 2) n <= 2
    have hratio0 : 0 <= (1 : Rat) / 2 := by decide +kernel
    have hratio1 : (1 : Rat) / 2 < 1 := by decide +kernel
    have h := geometricSum_le_inv_one_sub hratio0 hratio1 n
    have hden : (1 : Rat) / (1 - (1 : Rat) / 2) = 2 := by
      decide +kernel
    rw [hden] at h
    exact h
  · change (2 : Rat) <= 2
    exact Rat.le_refl

theorem geometricSum_eq (r : Rat) (hr : r ≠ 1) (n : Nat) :
    geometricSum r n = (r ^ n - 1) / (r - 1) := by
  have hne : r - 1 ≠ 0 := by
    intro h
    apply hr
    grind [Rat.sub_eq_add_neg]
  rw [Rat.div_def]
  calc
    geometricSum r n = geometricSum r n * 1 := by
      grind
    _ = geometricSum r n * ((r - 1) * (r - 1)⁻¹) := by
      rw [Rat.mul_inv_cancel (r - 1) hne]
    _ = ((r - 1) * geometricSum r n) * (r - 1)⁻¹ := by
      grind [Rat.mul_assoc, Rat.mul_comm]
    _ = (r ^ n - 1) * (r - 1)⁻¹ := by
      rw [geometricSum_mul_sub]

theorem geometricSum_le_of_le {r : Rat} (hr0 : 0 <= r)
    {n m : Nat} (hnm : n <= m) :
    geometricSum r n <= geometricSum r m := by
  induction hnm with
  | refl => exact Rat.le_refl
  | step _ ih =>
      exact Rat.le_trans ih (geometricSum_le_succ hr0 _)

theorem geometricSum_gap_le_of_le {r : Rat} (hr0 : 0 <= r) (hr1 : r < 1)
    {n m : Nat} (hnm : n <= m) :
    1 / (1 - r) - geometricSum r m <=
      1 / (1 - r) - geometricSum r n := by
  have hsum := geometricSum_le_of_le hr0 hnm
  grind

/-! A finite geometric certificate can be stated directly as a budget on the
remaining power.  This is the algorithm-facing form of the usual tail bound:
it certifies a rational gap to the finite upper endpoint without introducing
an infinite sum or a completed value. -/
theorem geometricSum_gap_le_of_power_budget {r eps : Rat} {n : Nat}
    (hr1 : r < 1)
    (hbudget : r ^ n <= eps * (1 - r)) :
    1 / (1 - r) - geometricSum r n <= eps := by
  have hden : 0 < (1 : Rat) - r := by grind
  have hinvnonneg : 0 <= (1 - r)⁻¹ :=
    Rat.le_of_lt ((Rat.inv_pos).2 hden)
  have hgap : 1 / (1 - r) - geometricSum r n =
      r ^ n * (1 - r)⁻¹ := by
    rw [Rat.div_def]
    grind [geometricSum_tail_eq r n, Rat.mul_assoc, Rat.mul_comm]
  calc
    1 / (1 - r) - geometricSum r n = r ^ n * (1 - r)⁻¹ := hgap
    _ <= (eps * (1 - r)) * (1 - r)⁻¹ := by
      exact Rat.mul_le_mul_of_nonneg_right hbudget hinvnonneg
    _ = eps := by
      have hcancel : (1 - r) * (1 - r)⁻¹ = 1 := by
        rw [Rat.mul_inv_cancel (1 - r) (Rat.ne_of_gt hden)]
      grind [Rat.mul_assoc, Rat.mul_comm]

/-! The power budget is also a complete finite-stage reachability
certificate for the rational approximation.  It exposes the two endpoints
that an algorithm computes, together with the certified width between them;
the statement remains entirely about one natural stage and exact rationals. -/
theorem geometricSum_finiteApprox_reaches_of_power_budget
    {r eps : Rat} {n : Nat}
    (hr0 : 0 <= r) (hr1 : r < 1)
    (hbudget : r ^ n <= eps * (1 - r)) :
    geometricSum r n <= 1 / (1 - r) /\
      1 / (1 - r) - geometricSum r n <= eps := by
  constructor
  · exact geometricSum_le_inv_one_sub hr0 hr1 n
  · exact geometricSum_gap_le_of_power_budget hr1 hbudget

/-! The budget can itself be selected effectively on the half-ratio branch.
The resulting theorem is still a finite statement: it returns one natural
stage for one requested rational tolerance, rather than introducing an
attained infinite sum. -/
theorem geometricSum_finiteApprox_reaches
    {r : Rat} (hr0 : 0 <= r) (hrhalf : r <= (1 : Rat) / 2)
    (hr1 : r < 1) (eps : QPos) :
    ∃ n : Nat,
      geometricSum r n <= 1 / (1 - r) /\
        1 / (1 - r) - geometricSum r n <= eps.val := by
  have hden : 0 < (1 : Rat) - r := by grind
  let target : QPos :=
    { val := eps.val * (1 - r)
      property := Rat.mul_pos eps.property hden }
  let n := RationalMajorant.halfDecayShift (1 : Rat) target
  have hhalf : ((1 : Rat) / 2) ^ n <= target.val := by
    have hshift := RationalMajorant.halfDecayShift_spec
      (bound := (1 : Rat)) (by decide +kernel : (0 : Rat) <= 1) target
    simpa [n, target] using hshift
  have hpow : r ^ n <= target.val :=
    Rat.le_trans (pow_le_half_pow hr0 hrhalf n) hhalf
  have hbudget : r ^ n <= eps.val * (1 - r) := by
    simpa [target] using hpow
  exact ⟨n, geometricSum_finiteApprox_reaches_of_power_budget
    hr0 hr1 hbudget⟩

/-! Rational binomial terms, with the Pascal split exposed before summation. -/

def binomialTerm (n k : Nat) (x y : Rat) : Rat :=
  (FiniteCounting.combination n k : Rat) * x ^ (n - k) * y ^ k

theorem binomialTerm_succ_succ_of_lt {n k : Nat} (hkn : k < n)
    (x y : Rat) :
    binomialTerm (n + 1) (k + 1) x y =
      x * binomialTerm n (k + 1) x y +
        y * binomialTerm n k x y := by
  unfold binomialTerm
  rw [FiniteCounting.combination_rat_pascal]
  have hpow₁ : n + 1 - (k + 1) = n - k := by omega
  have hpow₂ : n - (k + 1) + 1 = n - k := by omega
  have hxpow : x * x ^ (n - (k + 1)) =
      x ^ (n - (k + 1) + 1) := by
    rw [Rat.pow_succ]
    grind [Rat.mul_comm]
  have hypow : y * y ^ k = y ^ (k + 1) := by
    rw [Rat.pow_succ]
    grind [Rat.mul_comm]
  simp only [hpow₁]
  grind [Rat.mul_add, Rat.add_mul,
    Rat.mul_assoc, Rat.mul_comm]

def binomialSum (n : Nat) (x y : Rat) : Nat -> Rat
  | 0 => 0
  | k + 1 => binomialSum n x y k + binomialTerm n k x y

theorem binomialSum_succ (n k : Nat) (x y : Rat) :
    binomialSum n x y (k + 1) =
      binomialSum n x y k + binomialTerm n k x y := by
  rfl

theorem binomialSum_succ_row {n k : Nat} (hk : k <= n)
    (x y : Rat) :
    binomialSum (n + 1) x y (k + 1) =
      x * binomialSum n x y (k + 1) +
        y * binomialSum n x y k := by
  induction k generalizing n with
  | zero =>
      simp only [binomialSum]
      simp [binomialTerm, FiniteCounting.combination_zero_right]
      rw [Rat.pow_succ]
      grind [Rat.mul_assoc, Rat.mul_comm]
  | succ k ih =>
      have hkn : k < n := by omega
      change binomialSum (n + 1) x y (k + 1) +
          binomialTerm (n + 1) (k + 1) x y =
        x * (binomialSum n x y (k + 1) +
          binomialTerm n (k + 1) x y) +
          y * binomialSum n x y (k + 1)
      rw [ih (by omega), binomialSum_succ,
        binomialTerm_succ_succ_of_lt hkn]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

theorem binomialTerm_top (n : Nat) (x y : Rat) :
    binomialTerm n n x y = y ^ n := by
  simp [binomialTerm, FiniteCounting.combination_rat_self]

theorem binomialTerm_succ_top (n : Nat) (x y : Rat) :
    binomialTerm (n + 1) (n + 1) x y =
      y * binomialTerm n n x y := by
  rw [binomialTerm_top, binomialTerm_top]
  rw [Rat.pow_succ]
  grind [Rat.mul_comm]

theorem binomialSum_extra (n : Nat) (x y : Rat) :
    binomialSum n x y (n + 2) = binomialSum n x y (n + 1) := by
  rw [binomialSum_succ]
  unfold binomialTerm
  rw [FiniteCounting.combination_rat_outside n (n + 1) (by omega)]
  grind

theorem binomialSum_eq_pow (n : Nat) (x y : Rat) :
    binomialSum n x y (n + 1) = (x + y) ^ n := by
  induction n with
  | zero =>
      simp [binomialSum, binomialTerm,
        FiniteCounting.combination_zero_right]
      grind
  | succ n ih =>
      rw [binomialSum_succ,
        binomialSum_succ_row (n := n) (k := n) (Nat.le_refl n),
        binomialTerm_succ_top, Rat.add_assoc, ← Rat.mul_add,
        ← binomialSum_succ, ih]
      rw [Rat.pow_succ]
      grind [Rat.mul_add, Rat.add_mul, Rat.mul_assoc, Rat.mul_comm]

/-! Once the finite row has reached its last nonzero coefficient, every later
accumulator stage is definitionally the same value. -/
theorem binomialSum_eq_pow_of_reached
    {n count : Nat} (hcount : n + 1 <= count) (x y : Rat) :
    binomialSum n x y count = (x + y) ^ n := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases hprev : n + 1 <= count
      · rw [binomialSum_succ, ih hprev]
        have hout : n < count := by omega
        rw [binomialTerm, FiniteCounting.combination_rat_outside n count hout]
        simp
        grind
      · have hcount_eq : count = n := by omega
        subst count
        simpa using binomialSum_eq_pow n x y

theorem binomial_cube (x y : Rat) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

theorem binomial_square (x y : Rat) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  grind [Rat.pow_succ, Rat.mul_add, Rat.add_mul, Rat.mul_assoc,
    Rat.mul_comm, Rat.add_assoc, Rat.add_comm]

def triangularTelescopingTerm (n : Nat) : Rat :=
  2 / (n + 1) - 2 / (n + 2)

theorem triangularTelescopingTerm_eq_reciprocal (n : Nat) :
    triangularTelescopingTerm n =
      2 / (((n + 1 : Nat) : Rat) * ((n + 2 : Nat) : Rat)) := by
  have ha : ((n + 1 : Nat) : Rat) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have hb : ((n + 2 : Nat) : Rat) ≠ 0 := by
    exact_mod_cast (by omega : n + 2 ≠ 0)
  have hab : ((n + 1 : Nat) : Rat) * ((n + 2 : Nat) : Rat) ≠ 0 := by
    intro h
    rcases (Rat.mul_eq_zero.mp h) with hzero | hzero
    · exact ha hzero
    · exact hb hzero
  have hstep : ((n + 2 : Nat) : Rat) = ((n + 1 : Nat) : Rat) + 1 := by
    exact_mod_cast (by omega : n + 2 = (n + 1) + 1)
  unfold triangularTelescopingTerm
  rw [Rat.div_def, Rat.div_def, Rat.div_def]
  grind [Rat.mul_inv_cancel (((n + 1 : Nat) : Rat)) ha,
    Rat.mul_inv_cancel (((n + 2 : Nat) : Rat)) hb,
    Rat.mul_inv_cancel
      (((n + 1 : Nat) : Rat) * ((n + 2 : Nat) : Rat)) hab,
    Rat.mul_assoc, Rat.mul_comm, Rat.sub_eq_add_neg]

def triangularTelescopingSum : Nat -> Rat
  | 0 => 0
  | n + 1 => triangularTelescopingSum n + triangularTelescopingTerm n

theorem triangularTelescopingSum_succ (n : Nat) :
    triangularTelescopingSum (n + 1) =
      triangularTelescopingSum n + triangularTelescopingTerm n := by
  rfl

theorem triangularTelescopingSum_eq (n : Nat) :
    triangularTelescopingSum n = 2 - 2 / (n + 1) := by
  induction n with
  | zero =>
      decide +kernel
  | succ n ih =>
      rw [triangularTelescopingSum_succ, ih]
      unfold triangularTelescopingTerm
      simp only [Rat.natCast_add]
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

theorem triangularTelescopingSum_tail_eq (n : Nat) :
    2 - triangularTelescopingSum n = 2 / (n + 1) := by
  rw [triangularTelescopingSum_eq]
  grind

theorem triangularTelescopingSum_lt_two (n : Nat) :
    triangularTelescopingSum n < 2 := by
  rw [triangularTelescopingSum_eq]
  have hden : (0 : Rat) < (n : Rat) + 1 := by
    have hnrat : (0 : Rat) <= n := Rat.natCast_nonneg
    grind
  have htail : (0 : Rat) < 2 / (n + 1) := by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel) ((Rat.inv_pos).2 hden)
  grind

theorem one_div_nat_antitone_series {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (hnm : n <= m) :
    (1 / (m : Rat)) <= 1 / (n : Rat) := by
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * (m : Rat))
  · calc
      (1 / (m : Rat)) * ((n : Rat) * (m : Rat)) = (n : Rat) := by
        have hmne : (m : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (m : Rat) := by exact_mod_cast hnm
      _ = (1 / (n : Rat)) * ((n : Rat) * (m : Rat)) := by
        have hnne : (n : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hn) ((Rat.natCast_pos).2 hm)

theorem triangularTelescopingSum_le_two (n : Nat) :
    triangularTelescopingSum n <= 2 :=
  Rat.le_of_lt (triangularTelescopingSum_lt_two n)

theorem triangularTelescopingSum_mono {n m : Nat} (hnm : n <= m) :
    triangularTelescopingSum n <= triangularTelescopingSum m := by
  rw [triangularTelescopingSum_eq, triangularTelescopingSum_eq]
  have hleft : 0 < ((n + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (by omega)
  have hright : 0 < ((m + 1 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (by omega)
  have hinv := one_div_nat_antitone_series (n := n + 1) (m := m + 1)
    (by omega) (by omega) (by omega)
  rw [Rat.div_def, Rat.div_def] at hinv ⊢
  grind [Rat.mul_assoc, Rat.mul_comm]

def triangularTelescopingRaw : RealCompute where
  compute := fun n =>
    { lo := triangularTelescopingSum n, hi := 2 }

theorem triangularTelescopingRaw_valid :
    triangularTelescopingRaw.Valid := by
  have hbound : forall n : Nat,
      (triangularTelescopingRaw.compute n).width <=
        (2 : Rat) / ((n + 1 : Nat) : Rat) := by
    intro n
    change 2 - triangularTelescopingSum n <=
      (2 : Rat) / ((n + 1 : Nat) : Rat)
    rw [triangularTelescopingSum_tail_eq]
    simp only [Rat.natCast_add]
    exact Rat.le_refl
  refine ⟨?_, ?_, ?_⟩
  · intro n
    change 0 <= 2 - triangularTelescopingSum n
    grind [triangularTelescopingSum_le_two n]
  · intro n m hnm
    change triangularTelescopingSum n <= triangularTelescopingSum m /\
      triangularTelescopingSum m <= 2 /\ (2 : Rat) <= 2
    exact ⟨triangularTelescopingSum_mono hnm,
      triangularTelescopingSum_le_two m, Rat.le_refl⟩
  · intro eps
    let half : Rat := eps.val / 2
    have hhalf : 0 < half := by
      dsimp [half]
      rw [Rat.div_def]
      exact Rat.mul_pos eps.property ((Rat.inv_pos).2 (by decide +kernel))
    refine ⟨half.den, ?_⟩
    intro n hn
    change 2 - triangularTelescopingSum n <= eps.val
    rw [triangularTelescopingSum_tail_eq]
    have hbase : 1 / (((half.den + 1 : Nat) : Rat)) <= half :=
      one_div_den_succ_le_of_pos hhalf
    have hmono := one_div_nat_antitone_series
      (n := half.den + 1) (m := n + 1)
      (by omega) (by omega) (by omega)
    have hone : 1 / ((n + 1 : Nat) : Rat) <= half :=
      Rat.le_trans hmono hbase
    dsimp [half] at hone
    rw [Rat.div_def] at hone ⊢
    grind [Rat.mul_assoc, Rat.mul_comm]

theorem triangularTelescopingRaw_equiv_two :
    triangularTelescopingRaw.Equiv (RealCompute.ofRat 2) := by
  intro n
  apply (RealCompute.compareAt_overlap_iff triangularTelescopingRaw
    (RealCompute.ofRat 2) n n).2
  constructor
  · change triangularTelescopingSum n <= 2
    exact triangularTelescopingSum_le_two n
  · exact Rat.le_refl

/-! Publicly expose the finite stage selected by the raw shrinkage proof.
This keeps the triangular telescoping representation usable as an executable
potential-infinity approximation, rather than leaving its tolerance witness
buried inside `RealCompute.Valid`. -/
theorem triangularTelescopingRaw_reaches_of_positive_tolerance (eps : QPos) :
    ∃ n : Nat, (triangularTelescopingRaw.compute n).width <= eps.val := by
  rcases triangularTelescopingRaw_valid.2.2 eps with ⟨N, hN⟩
  exact ⟨N, hN N (Nat.le_refl N)⟩

def alternatingSign (n : Nat) : Rat :=
  if n % 2 = 0 then 1 else -1

def signedTerm (term : Nat -> Rat) (n : Nat) : Rat :=
  alternatingSign n * term n

def partialSum (term : Nat -> Rat) : Nat -> Rat
  | 0 => 0
  | n + 1 => partialSum term n + signedTerm term n

def intervalBetween (a b : Rat) : QInterval :=
  if a <= b then { lo := a, hi := b } else { lo := b, hi := a }

/-- The natural interval attached to a partial-sum algorithm:
at stage `n`, return the interval between the `2n`th and `(2n+1)`st
partial sums. -/
def evenOddInterval (partials : Nat -> Rat) (n : Nat) : QInterval :=
  intervalBetween (partials (2 * n)) (partials (2 * n + 1))

/-- Natural interval algorithm for an alternating series specified by term
magnitudes.  This deliberately uses the slow, transparent stage `n →[S_{2n}, S_{2n+1}]`; any faster convergence rate should be extra metadata,
not hidden in the representation. -/
def alternatingInterval (term : Nat -> Rat) (n : Nat) : QInterval :=
  evenOddInterval (partialSum term) n

theorem alternatingSign_even (n : Nat) :
    alternatingSign (2 * n) = 1 := by
  unfold alternatingSign
  have h : (2 * n) % 2 = 0 := by omega
  rw [h]
  rfl

theorem alternatingSign_add (n m : Nat) :
    alternatingSign (n + m) = alternatingSign n * alternatingSign m := by
  unfold alternatingSign
  by_cases hn : n % 2 = 0
  · by_cases hm : m % 2 = 0
    · have hnm : (n + m) % 2 = 0 := by omega
      simp [hn, hm, hnm]
    · have hnm : (n + m) % 2 ≠ 0 := by omega
      simp [hn, hm, hnm]
  · by_cases hm : m % 2 = 0
    · have hnm : (n + m) % 2 ≠ 0 := by omega
      simp [hn, hm, hnm]
    · have hnm : (n + m) % 2 = 0 := by omega
      simp [hn, hm, hnm]
      decide +kernel

/-! A finite block-transport law for alternating partial sums.  The factor
`alternatingSign n` records the phase at which the transported block starts;
the statement is entirely about natural recursion over rational terms. -/
theorem partialSum_add_block (term : Nat -> Rat) (n m : Nat) :
    partialSum term (n + m) =
      partialSum term n +
        alternatingSign n * partialSum (fun k => term (n + k)) m := by
  induction m with
  | zero =>
      rw [Nat.add_zero]
      change partialSum term n = partialSum term n +
        alternatingSign n * 0
      grind
  | succ m ihm =>
      rw [show n + (m + 1) = (n + m) + 1 by omega]
      rw [partialSum, ihm]
      rw [partialSum]
      unfold signedTerm
      rw [alternatingSign_add]
      grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm, Rat.add_assoc,
        Rat.add_comm]

theorem partialSum_even_succ (term : Nat -> Rat) (n : Nat) :
    partialSum term (2 * n + 1) = partialSum term (2 * n) + term (2 * n) := by
  rw [show 2 * n + 1 = (2 * n) + 1 by omega]
  simp [partialSum, signedTerm, alternatingSign_even]

theorem partialSum_even_step (term : Nat -> Rat) (n : Nat) :
    partialSum term (2 * (n + 1)) =
      partialSum term (2 * n) + term (2 * n) - term (2 * n + 1) := by
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
  rw [partialSum, partialSum_even_succ]
  simp [signedTerm, alternatingSign]
  grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm]

theorem partialSum_odd_step (term : Nat -> Rat) (n : Nat) :
    partialSum term (2 * (n + 1) + 1) =
      partialSum term (2 * n + 1) - term (2 * n + 1) + term (2 * (n + 1)) := by
  rw [show 2 * (n + 1) + 1 = (2 * (n + 1)) + 1 by omega]
  rw [partialSum, partialSum_even_step]
  simp [signedTerm, alternatingSign]
  rw [partialSum_even_succ]

/-- Data for an alternating series by magnitudes.

The interval at stage `n` is the interval between the `2n`th and `(2n+1)`st
partial sums.  The monotonicity field is not needed for the width-shrinking
theorem below, but it is the structural hypothesis that will later prove
nestedness and that these intervals enclose the same limit. -/
structure AlternatingRaw where
  term : Nat -> Rat
  term_nonneg : forall n, 0 <= term n
  term_decreasing : forall n, term (n + 1) <= term n
  term_shrinks : ShrinksToZero term

/-! The sine Taylor series is an alternating series once its rational input
has been enclosed in `[-2,2]`.  The term is kept as an absolute value here;
the signed partial sums are supplied by `AlternatingRaw.partialSum`. -/

def sineTermMagnitude (x : Rat) (k : Nat) : Rat :=
  qabs (FormalPowerSeries.sineTaylorTerm x k)

theorem sineTermMagnitude_eq_factorialTailTerm
    (x : Rat) (k : Nat) :
    sineTermMagnitude x k =
      RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) := by
  unfold sineTermMagnitude FormalPowerSeries.sineTaylorTerm
    RationalMajorant.factorialTailTerm
  rw [Rat.div_def, qabs_mul, qabs_mul,
    RationalMajorant.qabs_pow_eq_pow_qabs]
  have hsign : qabs (FormalPowerSeries.altSign k) = 1 := by
    unfold FormalPowerSeries.altSign
    split <;> decide +kernel
  rw [hsign]
  have hfactor : 0 <= (factorialRat (2 * k + 1))⁻¹ := by
    exact Rat.le_of_lt ((Rat.inv_pos).2
      (RationalMajorant.factorialRat_pos _))
  rw [qabs_eq_self_of_nonneg hfactor]
  simp [Rat.div_def]

theorem sineTermMagnitude_nonneg (x : Rat) (k : Nat) :
    0 <= sineTermMagnitude x k :=
  qabs_nonneg _

theorem halfPow_le_one (n : Nat) :
    ((1 : Rat) / 2) ^ n <= 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Rat.pow_succ]
      calc
        ((1 : Rat) / 2) ^ n * (1 / 2) <= 1 * (1 / 2) :=
          Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel)
        _ <= 1 * 1 :=
          Rat.mul_le_mul_of_nonneg_left (by decide +kernel) (by decide +kernel)
        _ = 1 := by decide +kernel

theorem halfPow_add_le_left (a b : Nat) :
    ((1 : Rat) / 2) ^ (a + b) <= ((1 : Rat) / 2) ^ a := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, Rat.pow_succ]
      calc
        ((1 : Rat) / 2) ^ (a + b) * (1 / 2) <=
            ((1 : Rat) / 2) ^ a * (1 / 2) :=
          Rat.mul_le_mul_of_nonneg_right ih (by decide +kernel)
        _ <= ((1 : Rat) / 2) ^ a * 1 :=
          Rat.mul_le_mul_of_nonneg_left (by decide +kernel)
            (Rat.pow_nonneg (by decide +kernel))
        _ = ((1 : Rat) / 2) ^ a := by simp

theorem sineTermMagnitude_decreasing {x : Rat} (hx : qabs x <= 2) (k : Nat) :
    sineTermMagnitude x (k + 1) <= sineTermMagnitude x k := by
  rw [sineTermMagnitude_eq_factorialTailTerm,
    sineTermMagnitude_eq_factorialTailTerm]
  rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by omega,
    RationalMajorant.factorialTailTerm_succ,
    RationalMajorant.factorialTailTerm_succ]
  have hC : 0 <= qabs x := qabs_nonneg x
  have hden1 : 0 < ((2 * k + 2 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (by omega)
  have hden2 : 0 < ((2 * k + 3 : Nat) : Rat) := by
    exact (Rat.natCast_pos).2 (by omega)
  have hratio1 : qabs x / ((2 * k + 2 : Nat) : Rat) <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := ((2 * k + 2 : Nat) : Rat))
    · calc
        qabs x * ((2 * k + 2 : Nat) : Rat)⁻¹ *
            ((2 * k + 2 : Nat) : Rat) = qabs x := by
              rw [Rat.mul_assoc,
                Rat.inv_mul_cancel _ (Rat.ne_of_gt hden1), Rat.mul_one]
        _ <= 2 := hx
        _ <= ((2 * k + 2 : Nat) : Rat) := by exact_mod_cast (by omega)
        _ = 1 * ((2 * k + 2 : Nat) : Rat) := by grind
    · exact hden1
  have hratio2 : qabs x / ((2 * k + 3 : Nat) : Rat) <= 1 := by
    apply Rat.le_of_mul_le_mul_right (c := ((2 * k + 3 : Nat) : Rat))
    · calc
        qabs x * ((2 * k + 3 : Nat) : Rat)⁻¹ *
            ((2 * k + 3 : Nat) : Rat) = qabs x := by
              rw [Rat.mul_assoc,
                Rat.inv_mul_cancel _ (Rat.ne_of_gt hden2), Rat.mul_one]
        _ <= 2 := hx
        _ <= ((2 * k + 3 : Nat) : Rat) := by exact_mod_cast (by omega)
        _ = 1 * ((2 * k + 3 : Nat) : Rat) := by grind
    · exact hden2
  have hterm0 : 0 <=
      RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) :=
    RationalMajorant.factorialTailTerm_nonneg hC _
  calc
    RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) *
        (qabs x / ((2 * k + 2 : Nat) : Rat)) *
        (qabs x / ((2 * k + 3 : Nat) : Rat)) <=
        RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) := by
      have hprod :
          qabs x / ((2 * k + 2 : Nat) : Rat) *
              (qabs x / ((2 * k + 3 : Nat) : Rat)) <= 1 * 1 :=
        calc
          qabs x / ((2 * k + 2 : Nat) : Rat) *
              (qabs x / ((2 * k + 3 : Nat) : Rat)) <=
              1 * (qabs x / ((2 * k + 3 : Nat) : Rat)) :=
            Rat.mul_le_mul_of_nonneg_right hratio1
              (Rat.mul_nonneg hC
                (Rat.le_of_lt ((Rat.inv_pos).2 hden2)))
          _ <= 1 * 1 :=
            Rat.mul_le_mul_of_nonneg_left hratio2 (by decide +kernel)
      calc
        _ = RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) *
            ((qabs x / ((2 * k + 2 : Nat) : Rat)) *
              (qabs x / ((2 * k + 3 : Nat) : Rat))) := by
                grind [Rat.mul_assoc]
        _ <= RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) * (1 * 1) :=
          Rat.mul_le_mul_of_nonneg_left hprod hterm0
        _ = RationalMajorant.factorialTailTerm (qabs x) (2 * k + 1) := by
          rw [Rat.mul_one, Rat.mul_one]

theorem sineTermMagnitude_shrinks {x : Rat} (hx : qabs x <= 2) :
    ShrinksToZero (sineTermMagnitude x) := by
  intro eps
  let C : Rat := qabs x
  let start : Nat := RationalMajorant.factorialTailStart C
  let shift : Nat := RationalMajorant.halfDecayShift
    (2 * RationalMajorant.factorialTailTerm C start) eps
  refine ⟨start + shift, ?_⟩
  intro n hn
  have hindex : start + shift <= 2 * n + 1 := by omega
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hindex
  have hC : 0 <= C := by
    dsimp [C]
    exact qabs_nonneg x
  have hstart := RationalMajorant.factorialTailStart_satisfies C
  have hgeom := RationalMajorant.factorialTailTerm_le_geometric_from_start
    hC hstart (shift + d)
  have hpow : ((1 : Rat) / 2) ^ (shift + d) <=
      ((1 : Rat) / 2) ^ shift :=
    halfPow_add_le_left shift d
  have hbound :
      RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ shift <= eps.val := by
    calc
      RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ shift <=
          (2 * RationalMajorant.factorialTailTerm C start) *
            ((1 : Rat) / 2) ^ shift := by
        exact Rat.mul_le_mul_of_nonneg_right
          (by grind [RationalMajorant.factorialTailTerm_nonneg hC start])
          (Rat.pow_nonneg (by decide +kernel))
      _ <= eps.val := by
        have hterm0 : 0 <=
            RationalMajorant.factorialTailTerm C start :=
          RationalMajorant.factorialTailTerm_nonneg hC start
        exact RationalMajorant.halfDecayShift_spec
          (Rat.mul_nonneg (by decide +kernel) hterm0) eps
  have hterm :
      RationalMajorant.factorialTailTerm C (start + shift + d) <= eps.val := by
    calc
      RationalMajorant.factorialTailTerm C (start + shift + d) <=
          RationalMajorant.factorialTailTerm C start *
            ((1 : Rat) / 2) ^ (shift + d) := by
        simpa [Nat.add_assoc] using hgeom
      _ <= RationalMajorant.factorialTailTerm C start *
          ((1 : Rat) / 2) ^ shift := by
        exact Rat.mul_le_mul_of_nonneg_left hpow
          (RationalMajorant.factorialTailTerm_nonneg hC start)
      _ <= eps.val := hbound
  rw [sineTermMagnitude_eq_factorialTailTerm]
  simpa [C, hd, Nat.add_assoc] using hterm

def leibnizTerm (n : Nat) : Rat :=
  1 / ((2 * n + 1 : Nat) : Rat)

theorem leibnizTerm_nonneg (n : Nat) : 0 <= leibnizTerm n := by
  exact Rat.le_of_lt (one_div_nat_pos (by omega))

theorem leibnizTerm_decreasing (n : Nat) :
    leibnizTerm (n + 1) <= leibnizTerm n := by
  unfold leibnizTerm
  apply one_div_nat_antitone_series (by omega) (by omega)
  omega

theorem leibnizTerm_le_one_div_succ (n : Nat) :
    leibnizTerm n <= 1 / ((n + 1 : Nat) : Rat) := by
  unfold leibnizTerm
  apply one_div_nat_antitone_series (by omega) (by omega)
  omega

theorem leibnizTerm_shrinks : ShrinksToZero leibnizTerm := by
  intro eps
  refine ⟨eps.val.den, ?_⟩
  intro n hn
  exact Rat.le_trans (leibnizTerm_le_one_div_succ n)
    (Rat.le_trans
      (one_div_nat_antitone_series
        (Nat.succ_pos eps.val.den) (by omega)
        (by omega))
      (one_div_den_succ_le_of_pos eps.property))

namespace AlternatingRaw

theorem even_partialSum_mono
    (S : AlternatingRaw) {n m : Nat} (hnm : n <= m) :
    partialSum S.term (2 * n) <= partialSum S.term (2 * m) := by
  induction hnm with
  | refl => exact Rat.le_refl
  | @step m hnm ih =>
      rw [partialSum_even_step]
      exact Rat.le_trans ih (by
        have hdec := S.term_decreasing (2 * m)
        grind [Rat.sub_eq_add_neg])

theorem odd_partialSum_antitone
    (S : AlternatingRaw) {n m : Nat} (hnm : n <= m) :
    partialSum S.term (2 * m + 1) <= partialSum S.term (2 * n + 1) := by
  induction hnm with
  | refl => exact Rat.le_refl
  | @step m hnm ih =>
      rw [partialSum_odd_step]
      exact Rat.le_trans (by
        have hdec₁ := S.term_decreasing (2 * m)
        have hdec₂ := S.term_decreasing (2 * m + 1)
        grind [Rat.sub_eq_add_neg]) ih

def interval (S : AlternatingRaw) (n : Nat) : QInterval :=
  alternatingInterval S.term n

def toRealCompute (S : AlternatingRaw) : RealCompute where
  compute := S.interval

theorem interval_width_eq (S : AlternatingRaw) (n : Nat) :
    (S.interval n).width = S.term (2 * n) := by
  have hsucc := partialSum_even_succ S.term n
  have hle :
      partialSum S.term (2 * n) <= partialSum S.term (2 * n + 1) := by
    rw [hsucc]
    grind [S.term_nonneg (2 * n)]
  simp [interval, alternatingInterval, evenOddInterval, intervalBetween,
    QInterval.width, hsucc]
  grind [Rat.sub_eq_add_neg]

theorem interval_width_nonneg (S : AlternatingRaw) (n : Nat) :
    0 <= (S.interval n).width := by
  rw [interval_width_eq]
  exact S.term_nonneg (2 * n)

theorem interval_eq_endpoints (S : AlternatingRaw) (n : Nat) :
    S.interval n =
      { lo := partialSum S.term (2 * n),
        hi := partialSum S.term (2 * n + 1) } := by
  have hle : partialSum S.term (2 * n) <=
      partialSum S.term (2 * n + 1) := by
    rw [partialSum_even_succ]
    grind [S.term_nonneg (2 * n)]
  simp [interval, alternatingInterval, evenOddInterval, intervalBetween, hle]

theorem intervals_nested
    (S : AlternatingRaw) {n m : Nat} (hnm : n <= m) :
    (S.interval n).ContainsInterval (S.interval m) := by
  rw [interval_eq_endpoints, interval_eq_endpoints]
  unfold QInterval.ContainsInterval
  exact ⟨S.even_partialSum_mono hnm,
    S.odd_partialSum_antitone hnm⟩

/-- The consecutive-partial-sum intervals of an alternating series shrink
whenever the term magnitudes shrink. -/
theorem intervals_shrink (S : AlternatingRaw) :
    ShrinksToZero (fun n => (S.interval n).width) := by
  intro eps
  rcases S.term_shrinks eps with ⟨N, hN⟩
  exact ⟨N, by
    intro n hn
    change (S.interval n).width <= eps.val
    rw [interval_width_eq]
    exact hN (2 * n) (by omega)⟩

theorem toRealCompute_valid (S : AlternatingRaw) :
    S.toRealCompute.Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact interval_width_nonneg S n
  · intro n m hnm
    have hcontain := intervals_nested S hnm
    unfold QInterval.ContainsInterval at hcontain
    have hordered : (S.interval m).lo <= (S.interval m).hi := by
      have hwidth := interval_width_nonneg S m
      change 0 <= (S.interval m).hi - (S.interval m).lo at hwidth
      grind
    exact ⟨hcontain.1, hordered, hcontain.2⟩
  · exact intervals_shrink S

def leibnizAlternatingRaw : AlternatingRaw where
  term := leibnizTerm
  term_nonneg := leibnizTerm_nonneg
  term_decreasing := leibnizTerm_decreasing
  term_shrinks := leibnizTerm_shrinks

theorem leibnizAlternatingRaw_valid :
    leibnizAlternatingRaw.toRealCompute.Valid :=
  leibnizAlternatingRaw.toRealCompute_valid

/-! The concrete Leibniz evaluator exposes the reciprocal stage budget used by
the potential-infinity interface.  This is a rate statement for the raw
intervals, not an identification with a completed real limit. -/
theorem leibnizAlternatingRaw_width_le_one_div_succ (n : Nat) :
    (leibnizAlternatingRaw.interval n).width <=
      1 / ((n + 1 : Nat) : Rat) := by
  rw [AlternatingRaw.interval_width_eq]
  simp only [leibnizAlternatingRaw]
  apply Rat.le_trans (leibnizTerm_le_one_div_succ (2 * n))
  apply one_div_nat_antitone_series (by omega) (by omega)
  omega

/-! The concrete Leibniz interval has an exact, finite reciprocal width.
This makes the stage budget visible without introducing a completed sum. -/
theorem leibnizAlternatingRaw_width_eq_reciprocal (n : Nat) :
    (leibnizAlternatingRaw.interval n).width =
      1 / ((4 * n + 1 : Nat) : Rat) := by
  rw [AlternatingRaw.interval_width_eq]
  simp only [leibnizAlternatingRaw, leibnizTerm]
  have hden : 2 * (2 * n) + 1 = 4 * n + 1 := by omega
  rw [hden]

theorem leibnizAlternatingRaw_width_le_of_budget {n : Nat} {eps : Rat}
    (hbudget : 1 / ((4 * n + 1 : Nat) : Rat) <= eps) :
    (leibnizAlternatingRaw.interval n).width <= eps := by
  rw [leibnizAlternatingRaw_width_eq_reciprocal n]
  exact hbudget

/-! The reciprocal width bound also supplies its own finite stage selector.
This is the executable tolerance interface for the Leibniz alternating
algorithm: a positive rational request is converted to a natural stage. -/
theorem leibnizAlternatingRaw_reaches_of_positive_tolerance (eps : QPos) :
    ∃ n : Nat, (leibnizAlternatingRaw.interval n).width <= eps.val := by
  refine ⟨eps.val.den, ?_⟩
  exact Rat.le_trans
    (leibnizAlternatingRaw_width_le_one_div_succ eps.val.den)
    (one_div_den_succ_le_of_pos eps.property)

def sineAlternatingRaw (x : Rat) (hx : qabs x <= 2) : AlternatingRaw where
  term := sineTermMagnitude x
  term_nonneg := sineTermMagnitude_nonneg x
  term_decreasing := sineTermMagnitude_decreasing hx
  term_shrinks := sineTermMagnitude_shrinks hx

theorem sineAlternatingRaw_valid (x : Rat) (hx : qabs x <= 2) :
    (sineAlternatingRaw x hx).toRealCompute.Valid :=
  (sineAlternatingRaw x hx).toRealCompute_valid

theorem sineAlternatingRaw_signedTerm_eq_sineTaylorTerm
    {x : Rat} (hx : 0 <= x) (k : Nat) :
    signedTerm (sineTermMagnitude x) k =
      FormalPowerSeries.sineTaylorTerm x k := by
  have hxabs : qabs x = x := qabs_eq_self_of_nonneg hx
  have hmag := sineTermMagnitude_eq_factorialTailTerm x k
  rw [hxabs] at hmag
  unfold signedTerm alternatingSign FormalPowerSeries.sineTaylorTerm
  unfold RationalMajorant.factorialTailTerm at hmag
  by_cases hk : k % 2 = 0
  · simp [hk, FormalPowerSeries.altSign, hmag]
  · simp [hk, FormalPowerSeries.altSign, hmag]
    grind [Rat.div_def, Rat.mul_assoc]

theorem sineAlternatingRaw_partial_eq_sineTaylorPartial
    {x : Rat} (hx : 0 <= x) (hterms : qabs x <= 2) (n : Nat) :
    partialSum (sineTermMagnitude x) n =
      FormalPowerSeries.sineTaylorPartial x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [partialSum, FormalPowerSeries.sineTaylorPartial, ih,
        sineAlternatingRaw_signedTerm_eq_sineTaylorTerm hx]

theorem sineAlternatingRaw_interval_eq_sineTaylorInterval
    {x : Rat} (hx : 0 <= x) (hterms : qabs x <= 2) (n : Nat) :
    (sineAlternatingRaw x hterms).interval n =
      evenOddInterval (FormalPowerSeries.sineTaylorPartial x) n := by
  unfold sineAlternatingRaw AlternatingRaw.interval alternatingInterval
  unfold evenOddInterval
  have h0 := sineAlternatingRaw_partial_eq_sineTaylorPartial hx hterms (2 * n)
  have h1 := sineAlternatingRaw_partial_eq_sineTaylorPartial hx hterms (2 * n + 1)
  rw [h0, h1]

end AlternatingRaw

end Series

end ComputableAnalysis


