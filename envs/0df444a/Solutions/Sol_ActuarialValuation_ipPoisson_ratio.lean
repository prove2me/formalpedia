-- Prove2me | solution 1 for ActuarialValuation.ipPoisson_ratio
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T19:06:42.61779+00:00
-- url     : https://prove2.me/submissions/95c34a66-7947-47aa-9111-0c815b38a9ae

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_ipPoisson

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (l : ℝ) (n : ℕ) : ((n+1:ℕ):ℝ)*ipPoisson l (n+1)=l*ipPoisson l n := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn : ((n+1:ℕ):ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  simp only [ipPoisson, pow_succ, Nat.factorial_succ, Nat.cast_mul]
  field_simp [hfac, hn]
