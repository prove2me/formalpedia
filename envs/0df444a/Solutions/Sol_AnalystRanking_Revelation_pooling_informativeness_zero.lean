-- Prove2me | solution 1 for AnalystRanking.Revelation.pooling_informativeness_zero
-- status  : ACCEPTED   (prove)
-- author  : @yuzhou
-- created : 2026-11-21T03:22:14.79851+00:00
-- url     : https://prove2.me/submissions/272b52cf-a081-465f-947d-f92d65bbc167

import Mathlib
import Definitions.Def_AnalystRanking_Revelation_informativeness

namespace AnalystRanking.Revelation


theorem _root_.solution (γ ρ q : ℝ) (σ : ℝ × ℝ) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1)
    (hσ1 : 0 ≤ σ.1) (hσ1' : σ.1 ≤ 1) (hσ2 : 0 ≤ σ.2) (hσ2' : σ.2 ≤ 1) (hpool : σ.1 + σ.2 = 1) :
    informativeness q γ ρ σ = 0 := by
  have hσ : σ.2 = 1 - σ.1 := by linarith
  let a : Bool → ℝ := fun b => if b then σ.1 else 1 - σ.1
  have hj (ω i j : Bool) : fcastJoint γ ρ σ ω i j = a i * a j := by
    cases ω <;> cases i <;> cases j <;>
      simp [fcastJoint, sigProb, sigMarg, fprob, a, hσ, Fintype.sum_bool] <;> ring
  have hterm (i j : Bool) :
      (q * fcastJoint γ ρ σ true i j) * ((1 - q) * fcastJoint γ ρ σ false i j) /
        (q * fcastJoint γ ρ σ true i j + (1 - q) * fcastJoint γ ρ σ false i j)
      = q * (1 - q) * (a i * a j) := by
    rw [hj, hj]
    let b := a i * a j
    change (q * b) * ((1 - q) * b) / (q * b + (1 - q) * b) = q * (1 - q) * b
    have hbden : q * b + (1 - q) * b = b := by ring
    rw [hbden]
    by_cases hb : b = 0
    · simp [hb]
    · apply (div_eq_iff hb).mpr
      ring
  have hv : expPostVar q γ ρ σ = q * (1 - q) := by
    unfold expPostVar
    simp only [hterm, Fintype.sum_bool, a, Bool.false_eq_true, if_false, if_true]
    ring
  have hq : q * (1 - q) ≠ 0 := by positivity
  simp [informativeness, hv, hq]
