-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.ou_gaussian_path_log_likelihood
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:29:42.54073+00:00
-- url     : https://prove2.me/submissions/04256d63-ea8f-4719-ba4a-3304de0c7a94

import Mathlib
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem solution
    (rate q Δ : ℝ) (hrate : 0 < rate) (hq : 0 < q) (hΔ : 0 < Δ)
    {n : ℕ} (hn : 0 < n) (x : Fin (n + 1) → ℝ) :
    let a : ℝ := Real.exp (-rate * Δ)
    let v : ℝ := q / (2 * rate) * (1 - Real.exp (-(2 * rate * Δ)))
    let ρ : Fin n → ℝ := fun k =>
      Real.exp (-((x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2) / (2 * v)) /
        Real.sqrt (2 * Real.pi * v)
    0 < v ∧
      (∀ k : Fin n, 0 < ρ k) ∧
      (-Real.log (∏ k : Fin n, ρ k) =
        ∑ k : Fin n,
          (Real.log (2 * Real.pi * v) / 2 +
            (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v))) := by
  let a : ℝ := Real.exp (-rate * Δ)
  let v : ℝ := q / (2 * rate) * (1 - Real.exp (-(2 * rate * Δ)))
  let ρ : Fin n → ℝ := fun k =>
    Real.exp (-((x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2) / (2 * v)) /
      Real.sqrt (2 * Real.pi * v)
  change 0 < v ∧ (∀ k : Fin n, 0 < ρ k) ∧
    (-Real.log (∏ k : Fin n, ρ k) =
      ∑ k : Fin n, (Real.log (2 * Real.pi * v) / 2 +
        (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v)))
  have he : Real.exp (-(2 * rate * Δ)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hpos : 0 < 2 * rate * Δ := by positivity
    linarith
  have hv : 0 < v := by
    dsimp [v]
    apply mul_pos (div_pos hq (by positivity))
    linarith
  have hfac : 0 < 2 * Real.pi * v := by positivity
  have hsqrt : 0 < Real.sqrt (2 * Real.pi * v) :=
    Real.sqrt_pos.2 hfac
  have hρ : ∀ k : Fin n, 0 < ρ k := by
    intro k
    dsimp [ρ]
    exact div_pos (Real.exp_pos _) hsqrt
  have hlog (k : Fin n) :
      -Real.log (ρ k) =
        Real.log (2 * Real.pi * v) / 2 +
          (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v) := by
    dsimp [ρ]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hsqrt)]
    rw [Real.log_exp, Real.log_sqrt (le_of_lt hfac)]
    ring
  refine ⟨hv, hρ, ?_⟩
  calc
    -Real.log (∏ k : Fin n, ρ k) =
        ∑ k : Fin n, -Real.log (ρ k) := by
          rw [Real.log_prod (fun k _ => ne_of_gt (hρ k))]
          simp only [Finset.sum_neg_distrib]
    _ = ∑ k : Fin n, (Real.log (2 * Real.pi * v) / 2 +
          (x (Fin.succ k) - a * x (Fin.castSucc k)) ^ 2 / (2 * v)) := by
          apply Finset.sum_congr rfl
          intro k _
          exact hlog k
