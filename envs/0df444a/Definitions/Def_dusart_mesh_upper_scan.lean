-- Prove2me | Definitions.Def_dusart_mesh_upper_scan
-- name    : dusart_mesh_upper_scan
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:51:43.577496+00:00
-- url     : https://prove2.me/theorems/a28472fb-5539-4d2a-b66e-6a8bd9c9513c
-- title:
--   Dusart finite mesh: UpperScan
-- statement:
--   The UpperScan component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_dusart_mesh_trial_prime
set_option maxHeartbeats 0

set_option maxRecDepth 200000

namespace DusartFiniteMesh.UpperScan

def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | n+1 => f (n+1)

@[simp] lemma forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) : forceNat n f = f n := by
  cases n <;> rfl

def normalize (m e : ℕ) : ℕ × ℕ :=
  if m < 2^128 then (m,e) else ((m+131071)/131072,e+17)

def step (n m e : ℕ) : ℕ × ℕ :=
  normalize (bif primeFlag n then m*n else m) e

def log2f : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, n => if n < 2 then 0 else 1+log2f fuel (n/2)

def check (n m e : ℕ) : Bool :=
  let c := log2f 128 m+1
  decide (m ≤ 2^c) && decide ((c+e)*6931471808 ≤ n*10000000000)

def scan : ℕ → ℕ → ℕ → ℕ → Bool × (ℕ × ℕ)
  | 0, _, m, e => (true,(m,e))
  | len+1, n, m, e =>
    forceNat (n+1) fun k =>
    let s := step k m e
    forceNat s.1 fun m' => forceNat s.2 fun e' =>
    let r := scan len k m' e'
    ((if 255 ≤ k then check k m' e' else true) && r.1,r.2)

lemma primorial_next (n : ℕ) :
    primorial (n+1) = primorial n * (if Nat.Prime (n+1) then n+1 else 1) := by
  simp only [primorial,Finset.prod_filter,Finset.prod_range_succ]

lemma normalize_upper (m e : ℕ) :
    m*2^e ≤ (normalize m e).1*2^(normalize m e).2 := by
  unfold normalize
  split_ifs
  · rfl
  · have hh : m ≤ ((m+131071)/131072)*131072 := by omega
    have hm := Nat.mul_le_mul_right (2^e) hh
    norm_num only [pow_add,show (2 : ℕ)^17=131072 by norm_num] at *
    nlinarith only [hm]

lemma step_upper (n m e : ℕ) (h : primorial n ≤ m*2^e) :
    primorial (n+1) ≤ (step (n+1) m e).1*2^(step (n+1) m e).2 := by
  rw [primorial_next]
  unfold step
  by_cases hp : Nat.Prime (n+1)
  · have hf : primeFlag (n+1)=true := (primeFlag_iff _).2 hp
    simp only [if_pos hp,hf,cond_true]
    have hh := Nat.mul_le_mul_right (n+1) h
    exact (by nlinarith only [hh] : primorial n*(n+1) ≤ (m*(n+1))*2^e).trans
      (normalize_upper _ _)
  · have hf : primeFlag (n+1)=false := by
      apply Bool.eq_false_iff.mpr
      exact fun ht => hp ((primeFlag_iff _).1 ht)
    simp only [if_neg hp,hf,cond_false,mul_one]
    exact h.trans (normalize_upper _ _)

lemma check_sound (n m e : ℕ) (h : primorial n ≤ m*2^e)
    (hc : check n m e = true) : Chebyshev.theta (n : ℝ) ≤ n := by
  unfold check at hc
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
  let c := log2f 128 m+1
  have hm : primorial n ≤ 2^(c+e) := by
    calc
      _ ≤ m*2^e := h
      _ ≤ 2^c*2^e := Nat.mul_le_mul_right _ hc.1
      _ = _ := (pow_add _ _ _).symm
  rw [Chebyshev.theta_eq_log_primorial,Nat.floor_natCast]
  have hp : (0 : ℝ) < (primorial n : ℝ) := by exact_mod_cast primorial_pos n
  have hpow : (primorial n : ℝ) ≤ (2 : ℝ)^(c+e) := by exact_mod_cast hm
  have hh := Real.log_le_log hp hpow
  rw [Real.log_pow] at hh
  have hl := mul_le_mul_of_nonneg_left Real.log_two_lt_d9.le
    (by positivity : (0 : ℝ) ≤ (c+e : ℕ))
  have hcheck : ((c+e : ℕ) : ℝ)*6931471808 ≤ (n : ℝ)*10000000000 := by
    exact_mod_cast hc.2
  exact hh.trans (by nlinarith only [hl,hcheck])

lemma scan_sound (len n m e : ℕ) (h : primorial n ≤ m*2^e)
    (hc : (scan len n m e).1 = true) :
    primorial (n+len) ≤ (scan len n m e).2.1*2^(scan len n m e).2.2 ∧
      ∀ k : ℕ, n < k → k ≤ n+len → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  induction len generalizing n m e with
  | zero =>
    constructor
    · simpa only [scan,Nat.add_zero] using h
    · intro k hk hkn
      omega
  | succ len ih =>
    have hs := step_upper n m e h
    simp only [scan,forceNat_eq] at hc
    change ((if 255 ≤ n+1 then check (n+1) (step (n+1) m e).1 (step (n+1) m e).2 else true) &&
      (scan len (n+1) (step (n+1) m e).1 (step (n+1) m e).2).1) = true at hc
    rw [Bool.and_eq_true] at hc
    have hi := ih (n+1) (step (n+1) m e).1 (step (n+1) m e).2 hs hc.2
    constructor
    · simpa only [scan,forceNat_eq,show n+(len+1)=n+1+len by omega] using hi.1
    · intro k hk hkn hk255
      by_cases he : k=n+1
      · subst k
        rw [if_pos hk255] at hc
        exact check_sound _ _ _ hs hc.1
      · exact hi.2 k (by omega) (by omega) hk255

lemma scan_add (l₁ l₂ n m e : ℕ) :
    scan (l₁+l₂) n m e =
      let r := scan l₁ n m e
      let s := scan l₂ (n+l₁) r.2.1 r.2.2
      (r.1 && s.1,s.2) := by
  induction l₁ generalizing n m e with
  | zero => simp only [Nat.zero_add,Nat.add_zero,scan,Bool.true_and]
  | succ l ih =>
    simp only [Nat.succ_add,scan,forceNat_eq]
    rw [ih]
    simp only [show n+(l+1)=n+1+l by omega,Bool.and_assoc]

lemma checked_block (len n m e mo eo : ℕ)
    (h : primorial n ≤ m*2^e)
    (hc : scan len n m e = (true,(mo,eo))) :
    primorial (n+len) ≤ mo*2^eo ∧
      ∀ k : ℕ, n < k → k ≤ n+len → 255 ≤ k → Chebyshev.theta (k : ℝ) ≤ k := by
  have hcheck : (scan len n m e).1 = true := congrArg Prod.fst hc
  have hs := scan_sound len n m e h hcheck
  rw [hc] at hs
  exact hs

end DusartFiniteMesh.UpperScan


