-- Prove2me | solution 1 for ActuarialValuation.ipPoi_PGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:40:32.635234+00:00
-- url     : https://prove2.me/submissions/a55c8668-02a9-4194-952c-d866dcf27c12

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_ipPoisson
import Definitions.Def_actuarial_ipCountPGF

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l z : ℝ) :
    ipCountPGF (ipPoisson l) z = Real.exp (l*(z-1)) := by
  calc
    ipCountPGF (ipPoisson l) z =
        ∑' n : ℕ, Real.exp (-l)*((l*z)^n/(Nat.factorial n : ℝ)) := by
      unfold ipCountPGF
      apply tsum_congr
      intro n
      dsimp [ipPoisson]
      rw [mul_pow]
      ring
    _ = Real.exp (-l)*(∑' n : ℕ, (l*z)^n/(Nat.factorial n : ℝ)) := by
      rw [tsum_mul_left]
    _ = Real.exp (-l)*Real.exp (l*z) := by
      congr 1
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    _ = Real.exp (l*(z-1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
