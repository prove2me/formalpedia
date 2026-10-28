-- Prove2me | solution 1 for AdaptiveCubic.SecondOrder.theorem_2_1_sigma_min
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:43:36.473338+00:00
-- url     : https://prove2.me/submissions/a8c8f5f0-72f3-4a01-9236-5f3ede3cb6d8

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_IsARCRun

open scoped RealInnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (γ₁ γ₂ η₁ η₂ : ℝ)
    (x s : ℕ → EuclideanSpace ℝ (Fin n)) (σ : ℕ → ℝ)
    (B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hrun : AdaptiveCubic.Cauchy.IsARCRun f γ₁ γ₂ η₁ η₂ x s σ B)
    (σmin : ℝ) (hσmin : 0 < σmin) (h211 : ∀ k, σmin ≤ σ k)
    (j : ℕ) (σbar : ℝ) (hσbar : 0 < σbar) (h212 : ∀ k ≤ j + 1, σ k ≤ σbar) :
    (((Finset.range (j + 1)).filter
        (fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) < η₁)).card : ℤ) ≤
      ⌈((((Finset.range (j + 1)).filter
            (fun k => η₁ ≤ AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k))).card : ℝ) + 1) *
        (1 / Real.log γ₁) * Real.log (σbar / σmin)⌉ := by
  set ρk : ℕ → ℝ := fun k => AdaptiveCubic.Cauchy.rho f (B k) (σ k) (x k) (s k) with hρk
  have hγ1 : 1 < γ₁ := hrun.1
  have hlg : 0 < Real.log γ₁ := Real.log_pos hγ1
  have hσpos : ∀ k, 0 < σ k := fun k => lt_of_lt_of_le hσmin (h211 k)
  have hstep := hrun.2.2.2.2.2.2.2.2.2
  set U : ℕ → ℕ := fun t => ((Finset.range t).filter (fun k => ρk k < η₁)).card with hU
  set S : ℕ → ℕ := fun t => ((Finset.range t).filter (fun k => η₁ ≤ ρk k)).card with hS
  have hL : Real.log (σmin / σbar) = Real.log σmin - Real.log σbar :=
    Real.log_div hσmin.ne' hσbar.ne'
  have hind : ∀ t, t ≤ j + 1 → Real.log (σ 0) + U t * Real.log γ₁ + S t * Real.log (σmin / σbar)
      ≤ Real.log (σ t) := by
    intro t
    induction t with
    | zero => intro _; simp [hU, hS]
    | succ t ih =>
      intro ht
      have ih' := ih (by omega)
      have hUs : U (t + 1) = U t + (if ρk t < η₁ then 1 else 0) := by
        simp only [hU, Finset.range_add_one, Finset.filter_insert]
        split_ifs <;> simp [Finset.card_insert_of_notMem]
      have hSs : S (t + 1) = S t + (if η₁ ≤ ρk t then 1 else 0) := by
        simp only [hS, Finset.range_add_one, Finset.filter_insert]
        split_ifs <;> simp [Finset.card_insert_of_notMem]
      by_cases hP : ρk t < η₁
      · have h1 : γ₁ * σ t ≤ σ (t + 1) := ((hstep t).2.2 hP).1
        have h2 : Real.log γ₁ + Real.log (σ t) ≤ Real.log (σ (t + 1)) := by
          rw [← Real.log_mul (by linarith) (hσpos t).ne']
          exact Real.log_le_log (mul_pos (by linarith) (hσpos t)) h1
        rw [hUs, hSs, if_pos hP, if_neg (not_le.mpr hP)]
        push_cast
        linarith
      · have hP' : η₁ ≤ ρk t := not_lt.mp hP
        have h1 : σmin / σbar * σ t ≤ σ (t + 1) := by
          have hσt : σ t ≤ σbar := h212 t (by omega)
          calc σmin / σbar * σ t ≤ σmin / σbar * σbar :=
                mul_le_mul_of_nonneg_left hσt (by positivity)
            _ = σmin := by field_simp
            _ ≤ σ (t + 1) := h211 _
        have h2 : Real.log (σmin / σbar) + Real.log (σ t) ≤ Real.log (σ (t + 1)) := by
          rw [← Real.log_mul (by positivity) (hσpos t).ne']
          exact Real.log_le_log (mul_pos (by positivity) (hσpos t)) h1
        rw [hUs, hSs, if_neg hP, if_pos hP']
        push_cast
        linarith
  have hfin := hind (j + 1) le_rfl
  have hσj : Real.log (σ (j + 1)) ≤ Real.log σbar := Real.log_le_log (hσpos _) (h212 _ le_rfl)
  have hσ0 : Real.log σmin ≤ Real.log (σ 0) := Real.log_le_log hσmin (h211 0)
  have hLL : Real.log (σbar / σmin) = Real.log σbar - Real.log σmin :=
    Real.log_div hσbar.ne' hσmin.ne'
  have hkey : (U (j + 1) : ℝ) * Real.log γ₁ ≤ ((S (j + 1) : ℝ) + 1) * Real.log (σbar / σmin) := by
    rw [hLL]; rw [hL] at hfin; nlinarith
  have hU' : (U (j + 1) : ℝ) ≤ ((S (j + 1) : ℝ) + 1) * (1 / Real.log γ₁) * Real.log (σbar / σmin) := by
    rw [mul_comm ((S (j + 1) : ℝ) + 1), mul_assoc, one_div_mul_eq_div, le_div_iff₀' hlg]
    linarith
  have := Int.le_ceil (((S (j + 1) : ℝ) + 1) * (1 / Real.log γ₁) * Real.log (σbar / σmin))
  have h2 : ((U (j + 1) : ℤ) : ℝ) ≤ (⌈((S (j + 1) : ℝ) + 1) * (1 / Real.log γ₁) *
      Real.log (σbar / σmin)⌉ : ℝ) := by
    push_cast; linarith
  exact_mod_cast h2
