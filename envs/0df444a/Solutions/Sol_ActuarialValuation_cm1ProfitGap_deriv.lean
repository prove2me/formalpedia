-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitGap_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:59:11.568705+00:00
-- url     : https://prove2.me/submissions/a07b8432-d649-4a01-9c9a-1d77b27a5174

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (a l : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) :
    deriv (cm1ProfitGap a l n) i =
      deriv (cm1CashflowPV a n) i - deriv (cm1CashflowPV l n) i := by
  have hpos : 1 + i ≠ 0 := by linarith
  have hdiff (c : ℕ → ℝ) (m : ℕ) :
      DifferentiableAt ℝ (cm1CashflowPV c m) i := by
    induction m with
    | zero =>
        change DifferentiableAt ℝ (fun _ : ℝ => (0 : ℝ)) i
        exact differentiableAt_const (0 : ℝ)
    | succ m ih =>
        have hbase : DifferentiableAt ℝ
            (fun x : ℝ => 1 + x) i := by fun_prop
        have hpow : DifferentiableAt ℝ
            (fun x : ℝ => (1 + x) ^ (m + 1)) i :=
          hbase.pow (m + 1)
        have hden : (1 + i) ^ (m + 1) ≠ 0 := pow_ne_zero _ hpos
        have hrecip : DifferentiableAt ℝ
            (fun x : ℝ => 1 / (1 + x) ^ (m + 1)) i :=
          (show DifferentiableAt ℝ (fun _ : ℝ => (1:ℝ)) i
            from differentiableAt_const (1 : ℝ)).div hpow hden
        have hlast : DifferentiableAt ℝ
            (fun x : ℝ => c m * cm1Discount x (m + 1)) i := by
          change DifferentiableAt ℝ
            (fun x : ℝ => c m * (1 / (1 + x) ^ (m + 1))) i
          have hc : DifferentiableAt ℝ (fun _ : ℝ => c m) i :=
            differentiableAt_const (c m)
          exact hc.mul hrecip
        have heq : cm1CashflowPV c (m + 1) =
            fun x => cm1CashflowPV c m x +
              c m * cm1Discount x (m + 1) := by
          funext x
          simp [cm1CashflowPV, Finset.sum_range_succ]
        rw [heq]
        exact ih.add hlast
  change deriv (fun x => cm1CashflowPV a n x -
    cm1CashflowPV l n x) i =
    deriv (cm1CashflowPV a n) i - deriv (cm1CashflowPV l n) i
  exact deriv_fun_sub (hdiff a n) (hdiff l n)
