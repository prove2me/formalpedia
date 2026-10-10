-- Prove2me | solution 1 for ActuarialValuation.cm1RedingtonImmunisation_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T07:30:54.923623+00:00
-- url     : https://prove2.me/submissions/b826d807-a146-4720-bb7d-9e70c6d44ac5

import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1Accum
import Definitions.Def_actuarial_cm1Discount
import Definitions.Def_actuarial_cm1CashflowPV
import Definitions.Def_actuarial_cm1ProfitGap
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation Filter Topology

theorem solution
    (assets liabilities : ℕ → ℝ) (n : ℕ) (i₀ : ℝ)
    (hi : -1 < i₀)
    (hPV : cm1ProfitGap assets liabilities n i₀ = 0)
    (hD : deriv (cm1ProfitGap assets liabilities n) i₀ = 0)
    (hC : 0 < deriv (deriv (cm1ProfitGap assets liabilities n)) i₀) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i : ℝ,
      |i-i₀| < ε → cm1CashflowPV liabilities n i ≤ cm1CashflowPV assets n i := by
  have hpos : 1 + i₀ ≠ 0 := by linarith
  have hcontpv (c : ℕ → ℝ) (m : ℕ) :
      ContinuousAt (cm1CashflowPV c m) i₀ := by
    induction m with
    | zero =>
        change ContinuousAt (fun _ : ℝ => (0 : ℝ)) i₀
        exact continuousAt_const
    | succ m ih =>
        have hpow : ContinuousAt
            (fun x : ℝ => (1 + x) ^ (m + 1)) i₀ :=
          (continuousAt_const.add continuousAt_id).pow (m + 1)
        have hden : (1 + i₀) ^ (m + 1) ≠ 0 := pow_ne_zero _ hpos
        have hrecip : ContinuousAt
            (fun x : ℝ => 1 / (1 + x) ^ (m + 1)) i₀ :=
          continuousAt_const.div hpow hden
        have hlast : ContinuousAt
            (fun x : ℝ => c m * cm1Discount x (m + 1)) i₀ := by
          change ContinuousAt (fun x : ℝ => c m * (1 / (1 + x) ^ (m + 1))) i₀
          exact continuousAt_const.mul hrecip
        have heq : cm1CashflowPV c (m + 1) =
            fun x => cm1CashflowPV c m x +
              c m * cm1Discount x (m + 1) := by
          funext x
          simp [cm1CashflowPV, Finset.sum_range_succ]
        rw [heq]
        exact ih.add hlast
  have hcont : ContinuousAt
      (cm1ProfitGap assets liabilities n) i₀ := by
    change ContinuousAt (fun x =>
      cm1CashflowPV assets n x - cm1CashflowPV liabilities n x) i₀
    exact (hcontpv assets n).sub (hcontpv liabilities n)
  have hmin : IsLocalMin (cm1ProfitGap assets liabilities n) i₀ :=
    isLocalMin_of_deriv_deriv_pos hC hD hcont
  have hevent : ∀ᶠ x in 𝓝 i₀,
      cm1ProfitGap assets liabilities n i₀ ≤
        cm1ProfitGap assets liabilities n x := hmin
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨ε, hε, ?_⟩
  intro i hdist
  have hnear' : cm1ProfitGap assets liabilities n i₀ ≤
      cm1ProfitGap assets liabilities n i := by
    apply hnear
    simpa only [Real.dist_eq] using hdist
  rw [hPV] at hnear'
  change 0 ≤ cm1CashflowPV assets n i -
    cm1CashflowPV liabilities n i at hnear'
  linarith

