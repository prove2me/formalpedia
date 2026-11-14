-- Prove2me | solution 1 for AltRegret.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T18:57:54.836066+00:00
-- url     : https://prove2.me/submissions/6766e560-b396-4315-8aa0-a9390d7aef4d

import Theorems.Thm_AltRegret_theorem_5
import Definitions.Def_AltRegret_altRegretAgainst

open AltRegret
open scoped BigOperators

/-- Evaluate the potential at the center of one coordinate. -/
private lemma coordinate_le_logSumSup {d : ℕ} (a v : Fin d → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (i : Fin d) :
    a i ≤ ⨆ θ : ℝ, Real.log (∑ j, Real.exp (a j - β * (v j - θ) ^ 2)) := by
  classical
  let w (θ : ℝ) (j : Fin d) := Real.exp (a j - β * (v j - θ) ^ 2)
  have hterm (θ : ℝ) : w θ i ≤ ∑ j, w θ j :=
    Finset.single_le_sum (f := w θ) (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)
  have hbounded : BddAbove (Set.range (fun θ : ℝ => Real.log (∑ j, w θ j))) := by
    refine ⟨Real.log (∑ j, Real.exp (a j)), ?_⟩
    rintro _ ⟨θ, rfl⟩
    apply Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (hterm θ))
    apply Finset.sum_le_sum
    intro j _
    exact Real.exp_le_exp.mpr (sub_le_self _ (mul_nonneg hβ (sq_nonneg _)))
  calc
    a i = Real.log (w (v i) i) := by simp [w]
    _ ≤ Real.log (∑ j, w (v i) j) := Real.log_le_log (Real.exp_pos _) (hterm (v i))
    _ ≤ ⨆ θ : ℝ, Real.log (∑ j, w θ j) := le_ciSup hbounded (v i)

/-- The regret of a simplex comparator is its average of the coordinate regrets. -/
private lemma comparator_regret_eq_sum {d : ℕ} (η β : ℝ) (c : ℕ → Fin d → ℝ)
    (T : ℕ) (u : Fin d → ℝ) (hu : ∑ i, u i = 1) :
    altRegretAgainst (play η β c) c T u = ∑ i, regretVector η β c T i * u i := by
  classical
  unfold altRegretAgainst regretVector
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, hu, mul_one]
  congr 1
  simp only [Finset.sum_mul]
  exact Finset.sum_comm

theorem solution {d : ℕ} (T : ℕ) (hT : 1 ≤ T) (c : ℕ → Fin d → ℝ)
    (hc : ∀ t, 1 ≤ t → t ≤ T → ∀ i, c t i ∈ Set.Icc (-1 : ℝ) 1)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d)) :
    altRegretAgainst (play (1 / 8) (1 / 32) c) c T u ≤ 8 * Real.log d := by
  have hΦ := theorem_5 (1 / 8) (1 / 32) (by norm_num) le_rfl (by norm_num) c T hT hc
  have hcoord (i : Fin d) : regretVector (1 / 8) (1 / 32) c T i ≤ 8 * Real.log d := by
    have hlower : (1 / 8 : ℝ) * regretVector (1 / 8) (1 / 32) c T i ≤
        potential (1 / 8) (1 / 32) c (T + 1) := by
      simpa only [potential, potentialObjective, Nat.add_sub_cancel] using
        coordinate_le_logSumSup (fun j => (1 / 8 : ℝ) * regretVector (1 / 8) (1 / 32) c T j)
          (lossAt c T) (1 / 32) (by norm_num) i
    linarith [hlower.trans (hΦ.1.trans hΦ.2)]
  rw [comparator_regret_eq_sum _ _ _ _ _ hu.2]
  calc
    _ ≤ ∑ i, (8 * Real.log d) * u i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcoord i) (hu.1 i)
    _ = 8 * Real.log d := by rw [← Finset.mul_sum, hu.2, mul_one]
