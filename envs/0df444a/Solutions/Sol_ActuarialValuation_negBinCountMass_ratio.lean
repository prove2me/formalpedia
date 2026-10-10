-- Prove2me | solution 1 for ActuarialValuation.negBinCountMass_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:13:03.889515+00:00
-- url     : https://prove2.me/submissions/50de6ba1-fc2b-4e9c-8213-4eb51a0e05cd

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_negBinCountMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (r n : ℕ) (p : ℝ)
  (hr : 0 < r) :
  (n + 1 : ℝ) * negBinCountMass r p (n + 1) =
    ((n + r : ℕ) : ℝ) * p * negBinCountMass r p n := by
  have hcoef : (n + 1) * Nat.choose (n + r) (n + 1) =
      (n + r) * Nat.choose (n + r - 1) n := by
    cases n with
    | zero => simp [Nat.choose_one_right]
    | succ k =>
      have htop1 : k + r + 1 - (k + 1) = r := by omega
      have htop2 : k + r - k = r := by omega
      have h1 := Nat.choose_succ_right_eq (k + r + 1) (k + 1)
      have h2 := Nat.choose_succ_right_eq (k + r) k
      have hp := Nat.choose_succ_succ (k + r) k
      rw [htop1] at h1
      rw [htop2] at h2
      have hp' : Nat.choose (k + r + 1) (k + 1) =
          Nat.choose (k + r) k + Nat.choose (k + r) (k + 1) := by
        simpa [Nat.add_assoc] using hp
      have hs : (k + 2) * Nat.choose (k + r + 1) (k + 2) =
          (k + 1 + r) * Nat.choose (k + r) (k + 1) := by
        calc
          (k + 2) * Nat.choose (k + r + 1) (k + 2) =
              Nat.choose (k + r + 1) (k + 2) * (k + 2) := Nat.mul_comm _ _
          _ = Nat.choose (k + r + 1) (k + 1) * r := h1
          _ = (Nat.choose (k + r) k + Nat.choose (k + r) (k + 1)) * r := by rw [hp']
          _ = (k + 1 + r) * Nat.choose (k + r) (k + 1) := by nlinarith
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
  have hcoefR : (n + 1 : ℝ) * (Nat.choose (n + r) (n + 1) : ℝ) =
      ((n + r : ℕ) : ℝ) * (Nat.choose (n + r - 1) n : ℝ) := by
    exact_mod_cast hcoef
  have htop : (n + 1) + r - 1 = n + r := by omega
  unfold negBinCountMass
  rw [htop, pow_succ]
  calc
    _ = ((n + 1 : ℝ) * (Nat.choose (n + r) (n + 1) : ℝ)) * p *
        (1 - p) ^ r * p ^ n := by ring
    _ = (((n + r : ℕ) : ℝ) * (Nat.choose (n + r - 1) n : ℝ)) * p *
        (1 - p) ^ r * p ^ n := by rw [hcoefR]
    _ = ((n + r : ℕ) : ℝ) * p *
        ((Nat.choose (n + r - 1) n : ℝ) * (1 - p) ^ r * p ^ n) := by ring
