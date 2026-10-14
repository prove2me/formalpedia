-- Prove2me | solution 1 for ActuarialValuation.svMean_tail_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:19:05.030619+00:00
-- url     : https://prove2.me/submissions/167ebf07-addb-4c8b-b093-c90f4fb0d5aa

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_actuarial_svFiniteMassMean
import Definitions.Def_actuarial_svFiniteTailMass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (p : ℕ → ℝ) (n : ℕ) : svFiniteMassMean p n = ∑ k ∈ Finset.range n, svFiniteTailMass p n k := by
  induction n with
  | zero =>
    simp [svFiniteMassMean, svFiniteTailMass]
  | succ n ih =>
    have htail (k : ℕ) (hk : k ∈ Finset.range n) :
        svFiniteTailMass p (n+1) k =
          svFiniteTailMass p n k + p (n+1) := by
      unfold svFiniteTailMass
      have hklt : k < n := Finset.mem_range.mp hk
      have hset : Finset.Icc (k+1) (n+1) =
          insert (n+1) (Finset.Icc (k+1) n) := by
        ext j
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n+1 ∉ Finset.Icc (k+1) n := by simp
      rw [hset, Finset.sum_insert hnot]
      ring
    have hlast : svFiniteTailMass p (n+1) n = p (n+1) := by
      simp [svFiniteTailMass]
    have hsum : (∑ k ∈ Finset.range n, svFiniteTailMass p (n+1) k) =
        (∑ k ∈ Finset.range n, svFiniteTailMass p n k) +
          (n : ℝ) * p (n+1) := by
      calc
        (∑ k ∈ Finset.range n, svFiniteTailMass p (n+1) k) =
            (∑ k ∈ Finset.range n, (svFiniteTailMass p n k + p (n+1))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact htail k hk
        _ = (∑ k ∈ Finset.range n, svFiniteTailMass p n k) +
            (∑ k ∈ Finset.range n, p (n+1)) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ k ∈ Finset.range n, svFiniteTailMass p n k) +
            (n : ℝ) * p (n+1) := by simp
    calc
      svFiniteMassMean p (n+1) =
          svFiniteMassMean p n + (((n+1 : ℕ) : ℝ) * p (n+1)) := by
        unfold svFiniteMassMean
        exact Finset.sum_range_succ (fun k => (k : ℝ) * p k) (n+1)
      _ = (∑ k ∈ Finset.range n, svFiniteTailMass p n k) +
          (((n+1 : ℕ) : ℝ) * p (n+1)) := by rw [ih]
      _ = (∑ k ∈ Finset.range n, svFiniteTailMass p (n+1) k) +
          svFiniteTailMass p (n+1) n := by
        rw [hsum, hlast]
        norm_num [Nat.cast_add]
        ring
      _ = ∑ k ∈ Finset.range (n+1), svFiniteTailMass p (n+1) k := by
        exact (Finset.sum_range_succ (fun k => svFiniteTailMass p (n+1) k) n).symm
