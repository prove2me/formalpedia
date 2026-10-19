-- Prove2me | Definitions.Def_dusart_mesh_trial_prime
-- name    : dusart_mesh_trial_prime
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-16T17:51:12.397396+00:00
-- url     : https://prove2.me/theorems/f3e949ca-90ca-4201-b0a0-90fcbcc7788a
-- title:
--   Dusart finite mesh: TrialPrime
-- statement:
--   The TrialPrime component of the finite certificate for the fourth-power logarithmic Chebyshev theta bound. This module supplies the data structures and necessary proved helper interfaces used by the finite verification. All supporting claims in this file include complete Lean proofs; imported platform theorems are already proved.
-- source:
--   Pierre Dusart, Explicit estimates of some functions over primes, Ramanujan J. 45 (2018), 227–251, Theorem 4.2 (k=4, eta=151.3, x0=2), pp. 234–237; DOI 10.1007/s11139-016-9839-4. Supporting finite mesh and proper-divisor certificate formalization for TaoFivePrimes.dusart_theta_log_four_finite_mesh_certificate.

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace DusartFiniteMesh.UpperScan

def trial : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel+1, n, d => if n < d*d then true else if n%d=0 then false else trial fuel n (d+1)

lemma trial_sound (fuel n d : ℕ) (hc : trial fuel n d = true) :
    ∀ k, d ≤ k → k < d+fuel → k*k ≤ n → ¬k ∣ n := by
  induction fuel generalizing d with
  | zero => intro k hk hkd; omega
  | succ fuel ih =>
    intro k hk hkd hsq
    by_cases hs : n < d*d
    · nlinarith
    by_cases hd : n%d=0
    · simp only [trial,if_neg hs,if_pos hd,Bool.false_eq_true] at hc
    have hc' : trial fuel n (d+1)=true := by simpa only [trial,if_neg hs,if_neg hd] using hc
    by_cases he : k=d
    · subst k
      exact fun hv => hd (Nat.mod_eq_zero_of_dvd hv)
    · exact ih (d+1) hc' k (by omega) (by omega) hsq

lemma trial_prime (fuel n d : ℕ) (hn : Nat.Prime n) (hd : 2 ≤ d) : trial fuel n d=true := by
  induction fuel generalizing d with
  | zero => rfl
  | succ fuel ih =>
    by_cases hs : n < d*d
    · simp only [trial,if_pos hs]
    have hnott : ¬d ∣ n := (Nat.prime_def_le_sqrt.1 hn).2 d hd (Nat.le_sqrt.2 (by omega))
    have hmod : n%d≠0 := fun hh => hnott (Nat.dvd_of_mod_eq_zero hh)
    simpa only [trial,if_neg hs,if_neg hmod] using ih (d+1) (by omega)

def primeFlag (n : ℕ) : Bool := decide (2 ≤ n) && trial n n 2

lemma primeFlag_iff (n : ℕ) : primeFlag n=true ↔ Nat.Prime n := by
  constructor
  · intro hc
    unfold primeFlag at hc
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
    refine Nat.prime_def_le_sqrt.2 ⟨hc.1,?_⟩
    intro k hk hks
    have hkn : k ≤ n := hks.trans (Nat.sqrt_le_self n)
    exact trial_sound n n 2 hc.2 k hk (by omega) (Nat.le_sqrt.1 hks)
  · intro hp
    unfold primeFlag
    simp only [hp.two_le,decide_true,Bool.true_and]
    exact trial_prime n n 2 hp le_rfl

end DusartFiniteMesh.UpperScan


