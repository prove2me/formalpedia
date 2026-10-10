-- Prove2me | solution 1 for ActuarialValuation.cm1ProfitGap_second_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:36:13.598807+00:00
-- url     : https://prove2.me/submissions/99a8a64d-388c-4df8-8b57-8a4730221616

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation Filter Topology

theorem solution (a l : ℕ → ℝ) (n : ℕ) (i : ℝ) (hi : -1 < i) :
    deriv (deriv (cm1ProfitGap a l n)) i =
      deriv (deriv (cm1CashflowPV a n)) i -
      deriv (deriv (cm1CashflowPV l n)) i := by
  have hsmooth (c : ℕ → ℝ) (m : ℕ) (x : ℝ) (hx : -1 < x) :
      ContDiffAt ℝ 2 (cm1CashflowPV c m) x := by
    have hpos : 1 + x ≠ 0 := by linarith
    induction m with
    | zero =>
        change ContDiffAt ℝ 2 (fun _ : ℝ => (0 : ℝ)) x
        exact contDiffAt_const
    | succ m ih =>
        have hbase : ContDiffAt ℝ 2
            (fun y : ℝ => 1 + y) x := by fun_prop
        have hpow : ContDiffAt ℝ 2
            (fun y : ℝ => (1 + y) ^ (m + 1)) x :=
          hbase.pow (m + 1)
        have hden : (1 + x) ^ (m + 1) ≠ 0 := pow_ne_zero _ hpos
        have hrecip : ContDiffAt ℝ 2
            (fun y : ℝ => 1 / (1 + y) ^ (m + 1)) x :=
          (show ContDiffAt ℝ 2 (fun _ : ℝ => (1:ℝ)) x
            from contDiffAt_const).div hpow hden
        have hlast : ContDiffAt ℝ 2
            (fun y : ℝ => c m * cm1Discount y (m + 1)) x := by
          change ContDiffAt ℝ 2
            (fun y : ℝ => c m * (1 / (1 + y) ^ (m + 1))) x
          have hc : ContDiffAt ℝ 2 (fun _ : ℝ => c m) x :=
            contDiffAt_const
          exact hc.mul hrecip
        have heq : cm1CashflowPV c (m + 1) =
            fun y => cm1CashflowPV c m y +
              c m * cm1Discount y (m + 1) := by
          funext y
          simp [cm1CashflowPV, Finset.sum_range_succ]
        rw [heq]
        exact ih.add hlast
  have hfirst (x : ℝ) (hx : -1 < x) :
      deriv (cm1ProfitGap a l n) x =
        deriv (cm1CashflowPV a n) x -
        deriv (cm1CashflowPV l n) x := by
    change deriv (fun y => cm1CashflowPV a n y -
      cm1CashflowPV l n y) x =
      deriv (cm1CashflowPV a n) x - deriv (cm1CashflowPV l n) x
    exact deriv_fun_sub
      ((hsmooth a n x hx).differentiableAt (by norm_num))
      ((hsmooth l n x hx).differentiableAt (by norm_num))
  have ha : DifferentiableAt ℝ (deriv (cm1CashflowPV a n)) i := by
    have hh : ContDiffAt ℝ 1 (deriv (cm1CashflowPV a n)) i :=
      (hsmooth a n i hi).derivWithin (by norm_num)
    exact hh.differentiableAt_one
  have hl : DifferentiableAt ℝ (deriv (cm1CashflowPV l n)) i := by
    have hh : ContDiffAt ℝ 1 (deriv (cm1CashflowPV l n)) i :=
      (hsmooth l n i hi).derivWithin (by norm_num)
    exact hh.differentiableAt_one
  have hopen : {x : ℝ | -1 < x} ∈ 𝓝 i :=
    isOpen_Ioi.mem_nhds hi
  have hevent : (fun x => deriv (cm1ProfitGap a l n) x) =ᶠ[𝓝 i]
      (fun x => deriv (cm1CashflowPV a n) x -
        deriv (cm1CashflowPV l n) x) :=
    Filter.eventually_of_mem hopen (fun x hx => hfirst x hx)
  calc
    deriv (deriv (cm1ProfitGap a l n)) i =
        deriv (fun x => deriv (cm1CashflowPV a n) x -
          deriv (cm1CashflowPV l n) x) i :=
      hevent.deriv_eq
    _ = deriv (deriv (cm1CashflowPV a n)) i -
        deriv (deriv (cm1CashflowPV l n)) i :=
      deriv_fun_sub ha hl


