-- Prove2me | solution 1 for ActuarialValuation.ipPoi_normalized
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:38:48.838494+00:00
-- url     : https://prove2.me/submissions/32efedc9-6657-4330-983f-6d33891f4b33

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipPoisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℝ) :
    (∑' n : ℕ, ipPoisson l n) = 1 := by
  calc
    (∑' n : ℕ, ipPoisson l n) =
        ∑' n : ℕ, Real.exp (-l)*(l^n/(Nat.factorial n : ℝ)) := by
      apply tsum_congr
      intro n
      dsimp [ipPoisson]
      ring
    _ = Real.exp (-l)*(∑' n : ℕ, l^n/(Nat.factorial n : ℝ)) := by
      rw [tsum_mul_left]
    _ = Real.exp (-l)*Real.exp l := by
      congr 1
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
