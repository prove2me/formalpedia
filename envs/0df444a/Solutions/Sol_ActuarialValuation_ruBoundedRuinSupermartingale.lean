-- Prove2me | solution 1 for ActuarialValuation.ruBoundedRuinSupermartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T17:30:03.4753+00:00
-- url     : https://prove2.me/submissions/02eacf4e-4b87-4b22-9d1e-09b3be64f693

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Definitions.Def_actuarial_ruStoppedIncrementMean
import Definitions.Def_actuarial_ruExponentialSurplus
import Definitions.Def_actuarial_ruTerminalExponentialMean
import Definitions.Def_actuarial_ruSurplus
import Definitions.Def_actuarial_ruFiniteRuinBound
import Definitions.Def_actuarial_ruMean
import Definitions.Def_actuarial_ruStopped
import Definitions.Def_actuarial_ruExpectedStopped

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {m : ℕ} (p : Fin m → ℝ) (u R : ℝ) (G : ℕ → Fin m → ℝ)
    (τ : Fin m → ℕ) (N : ℕ) (hτ : ∀ ω, τ ω ≤ N) (hn : (∑ ω : Fin m, p ω) = 1)
    (hinc : ∀ k ∈ Finset.range N,
      ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ k ≤ 0) :
    ruTerminalExponentialMean p R (fun ω => ruSurplus u G (τ ω) ω)
      ≤ ruFiniteRuinBound R u := by
  have hsuper : ruExpectedStopped p (ruExponentialSurplus u R G) τ N
      ≤ ruMean p ((ruExponentialSurplus u R G) 0) := by
    have htel : ∀ N : ℕ,
        ruExpectedStopped p (ruExponentialSurplus u R G) τ N
          = ruExpectedStopped p (ruExponentialSurplus u R G) τ 0
            + ∑ k ∈ Finset.range N,
              ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ k := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have hbal : ruExpectedStopped p (ruExponentialSurplus u R G) τ (n+1)
            = ruExpectedStopped p (ruExponentialSurplus u R G) τ n
              + ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ n := by
          unfold ruExpectedStopped ruStoppedIncrementMean ruMean
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro ω hω
          ring
        rw [hbal, ih, Finset.sum_range_succ]
        ring
    have h0 : ruExpectedStopped p (ruExponentialSurplus u R G) τ 0
        = ruMean p ((ruExponentialSurplus u R G) 0) := by
      unfold ruExpectedStopped ruMean
      apply Finset.sum_congr rfl
      intro ω hω
      congr 1
      try (simp [ruStopped])
    have hsum : ∑ k ∈ Finset.range N,
        ruStoppedIncrementMean p (ruExponentialSurplus u R G) τ k ≤ 0 :=
      Finset.sum_nonpos (fun k hk => hinc k hk)
    rw [htel N, h0]
    linarith
  have hfreeze : ruTerminalExponentialMean p R (fun ω => ruSurplus u G (τ ω) ω)
      = ruExpectedStopped p (ruExponentialSurplus u R G) τ N := by
    unfold ruTerminalExponentialMean ruExpectedStopped ruMean
    apply Finset.sum_congr rfl
    intro ω hω
    have hτω : τ ω ≤ N := hτ ω
    have hmin : min N (τ ω) = τ ω := by omega
    simp only [ruStopped, ruExponentialSurplus, ruExponential, hmin]
  have hinit : ruMean p ((ruExponentialSurplus u R G) 0)
      = ruFiniteRuinBound R u := by
    unfold ruMean ruExponentialSurplus ruExponential ruFiniteRuinBound
    have e0 : ∀ ω ∈ Finset.univ,
        p ω * Real.exp (-R * ruSurplus u G 0 ω)
          = Real.exp (-R * u) * p ω := by
      intro ω _
      have s0 : ruSurplus u G 0 ω = u := by
        unfold ruSurplus
        simp
      rw [s0]
      ring
    have step1 : (∑ ω : Fin m, p ω * Real.exp (-R * ruSurplus u G 0 ω))
        = ∑ ω : Fin m, Real.exp (-R * u) * p ω := Finset.sum_congr rfl e0
    have step2 : (∑ ω : Fin m, Real.exp (-R * u) * p ω)
        = Real.exp (-R * u) * ∑ ω : Fin m, p ω := (Finset.mul_sum _ _ _).symm
    have step3 : Real.exp (-R * u) * ∑ ω : Fin m, p ω
        = Real.exp (-R * u) := by
      rw [hn, mul_one]
    exact step1.trans (step2.trans step3)
  rw [hfreeze]
  exact le_trans hsuper (le_of_eq hinit)
