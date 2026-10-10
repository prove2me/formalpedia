-- Prove2me | solution 1 for ActuarialValuation.wholeLifeFiniteVariance_allocation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:05:27.306326+00:00
-- url     : https://prove2.me/submissions/05f475f7-398c-41f6-b2b9-3465e0ef7437

import Mathlib
import Definitions.Def_actuarial_wholeLifeFiniteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_orthogonal
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_second_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (w rho : ℕ → ℝ) (n : ℕ)
  (hw : Summable w)
  (hS : ∀ t, 0 < wholeLifeTailMass w t) :
  (∑' k : ℕ, w k * (wholeLifeFiniteInnovation w rho n k) ^ 2) =
    ∑ t ∈ Finset.range n,
      (rho t) ^ 2 * w t *
        (wholeLifeTailMass w (t + 1) / wholeLifeTailMass w t) := by
  classical
  let I (t k : ℕ) : ℝ := wholeLifeYearInnovation w t k
  let s : Finset ℕ := Finset.range n
  have hbound (t k : ℕ) :
      |I t k| ≤ 1 + |w t / wholeLifeTailMass w t| := by
    by_cases hkt : k = t
    · subst k
      simpa [I, wholeLifeYearInnovation] using
        (abs_sub_le (1 : ℝ) 0 (w t / wholeLifeTailMass w t))
    · by_cases htk : t ≤ k
      · simp [I, wholeLifeYearInnovation, hkt, htk]
      · simp [I, wholeLifeYearInnovation, hkt, htk]
        positivity
  have hpair (i j : ℕ) :
      Summable (fun k : ℕ => w k * I i k * I j k) := by
    let C : ℝ := (1 + |w i / wholeLifeTailMass w i|) *
      (1 + |w j / wholeLifeTailMass w j|)
    have hs : Summable (fun k : ℕ => C * ‖w k‖) :=
      (hw.norm).mul_left C
    apply hs.of_norm_bounded
    intro k
    have hb : |I i k * I j k| ≤ C := by
      dsimp [C]
      rw [abs_mul]
      exact mul_le_mul (hbound i k) (hbound j k)
        (abs_nonneg _) (by positivity)
    calc
      ‖w k * I i k * I j k‖ = ‖w k‖ * |I i k * I j k| := by
        simp [Real.norm_eq_abs, abs_mul, mul_assoc]
      _ ≤ ‖w k‖ * C := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = C * ‖w k‖ := mul_comm _ _
  have hcorr (i j : ℕ) :
      (∑' k : ℕ, w k * I i k * I j k) =
        if i = j then
          w i * (wholeLifeTailMass w (i + 1) / wholeLifeTailMass w i)
        else 0 := by
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      calc
        _ = ∑' k : ℕ, w k * (wholeLifeYearInnovation w i k) ^ 2 := by
          apply tsum_congr
          intro k
          dsimp [I]
          ring
        _ = _ := wholeLifeYearInnovation_second_moment w i hw (hS i)
    · by_cases hlt : i < j
      · simp only [if_neg hij]
        simpa only [I] using
          (wholeLifeYearInnovation_orthogonal w i j hw hlt (hS i) (hS j))
      · have hgt : j < i := by omega
        simp only [if_neg hij]
        calc
          _ = ∑' k : ℕ, w k * I j k * I i k := by
            apply tsum_congr
            intro k
            ring
          _ = 0 := by simpa only [I] using
            (wholeLifeYearInnovation_orthogonal w j i hw hgt (hS j) (hS i))
  let F (i j k : ℕ) : ℝ :=
    rho i * rho j * (w k * I i k * I j k)
  have hF (i j : ℕ) : Summable (F i j) := (hpair i j).mul_left _
  have hfin (q : Finset ℕ) (g : ℕ → ℕ → ℝ)
      (hg : ∀ i ∈ q, Summable (g i)) :
      Summable (fun k => ∑ i ∈ q, g i k) := by
    classical
    revert hg
    induction q using Finset.induction_on with
    | empty =>
      intro hg
      simp
    | @insert a q ha ih =>
      intro hg
      have hqa : ∀ i ∈ q, Summable (g i) := by
        intro i hi
        exact hg i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using
        (hg a (Finset.mem_insert_self _ _)).add (ih hqa)
  have hsq (k : ℕ) :
      w k * (∑ i ∈ s, rho i * I i k) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, F i j k := by
    dsimp [F]
    calc
      _ = w k * ((∑ i ∈ s, rho i * I i k) *
          (∑ j ∈ s, rho j * I j k)) := by ring
      _ = _ := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  change (∑' k : ℕ, w k * (∑ i ∈ s, rho i * I i k) ^ 2) =
    ∑ i ∈ s, (rho i) ^ 2 * w i *
      (wholeLifeTailMass w (i + 1) / wholeLifeTailMass w i)
  calc
    _ = ∑' k : ℕ, ∑ i ∈ s, ∑ j ∈ s, F i j k := by
      apply tsum_congr
      intro k
      exact hsq k
    _ = ∑ i ∈ s, ∑ j ∈ s, ∑' k : ℕ, F i j k := by
      rw [Summable.tsum_finsetSum (fun i hi =>
        hfin s (F i) (by intro j hj; exact hF i j))]
      apply Finset.sum_congr rfl
      intro i hi
      exact Summable.tsum_finsetSum (fun j hj => hF i j)
    _ = ∑ i ∈ s, (rho i) ^ 2 * w i *
        (wholeLifeTailMass w (i + 1) / wholeLifeTailMass w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hinner :
        (∑ j ∈ s, ∑' k : ℕ, F i j k) =
          rho i * rho i *
            (w i * (wholeLifeTailMass w (i + 1) / wholeLifeTailMass w i)) := by
        calc
          _ = ∑ j ∈ s, rho i * rho j *
              (if i = j then w i *
                (wholeLifeTailMass w (i + 1) / wholeLifeTailMass w i)
              else 0) := by
                apply Finset.sum_congr rfl
                intro j hj
                dsimp [F]
                rw [tsum_mul_left, hcorr i j]
          _ = _ := by
            simp [mul_ite, hi, Finset.sum_ite_eq', eq_comm]
      nlinarith [hinner]
