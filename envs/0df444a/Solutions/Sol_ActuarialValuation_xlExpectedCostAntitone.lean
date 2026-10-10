-- Prove2me | solution 1 for ActuarialValuation.xlExpectedCostAntitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T15:20:06.59135+00:00
-- url     : https://prove2.me/submissions/7d3e2d76-0779-4e36-b91e-9006cda4594c

import Mathlib
import Definitions.Def_actuarial_xlExpectedValuePremiumCost
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w z : Ω → ℝ) (a b θ : ℝ)
  (hw : ∀ ω, 0 ≤ w ω) (hθ : 0 ≤ θ) (hab : a ≤ b)
  :
  xlExpectedValuePremiumCost w z b θ ≤ xlExpectedValuePremiumCost w z a θ := by
  classical
  have hsplit (r : ℝ) :
      xlExpectedValuePremiumCost w z r θ =
        xlExpectedLoss w z +
          θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) r) := by
    have heq : xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) r) +
      xlExpectedLoss w (fun ω => xlCededLoss (z ω) r) =
      xlExpectedLoss w z := by
      change (∑ ω : Ω, w ω * xlRetainedLoss (z ω) r) +
        (∑ ω : Ω, w ω * xlCededLoss (z ω) r) =
        ∑ ω : Ω, w ω * z ω
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ω hω
      simp only [xlRetainedLoss, xlCededLoss]
      ring
    unfold xlExpectedValuePremiumCost
    calc
      _ = (xlExpectedLoss w (fun ω => xlRetainedLoss (z ω) r) +
             xlExpectedLoss w (fun ω => xlCededLoss (z ω) r)) +
             θ * xlExpectedLoss w (fun ω => xlCededLoss (z ω) r) := by ring
      _ = _ := by rw [heq]
  have hceded : xlExpectedLoss w (fun ω => xlCededLoss (z ω) b) ≤
      xlExpectedLoss w (fun ω => xlCededLoss (z ω) a) := by
    change (∑ ω : Ω, w ω * xlCededLoss (z ω) b) ≤
      ∑ ω : Ω, w ω * xlCededLoss (z ω) a
    apply Finset.sum_le_sum
    intro ω hω
    apply mul_le_mul_of_nonneg_left _ (hw ω)
    change z ω - min (z ω) b ≤ z ω - min (z ω) a
    have hmin : min (z ω) a ≤ min (z ω) b :=
      min_le_min_left (z ω) hab
    linarith
  rw [hsplit b, hsplit a]
  exact add_le_add_right (mul_le_mul_of_nonneg_left hceded hθ) _
