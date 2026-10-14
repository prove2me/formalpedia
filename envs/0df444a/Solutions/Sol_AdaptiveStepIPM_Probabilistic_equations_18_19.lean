-- Prove2me | solution 1 for AdaptiveStepIPM.Probabilistic.equations_18_19
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T05:25:29.048925+00:00
-- url     : https://prove2.me/submissions/a1af7305-3ca7-442f-852d-0d41ec1074c3

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter


namespace AdaptiveStepIPM.Probabilistic

theorem abs_le_supNorm_core {n : ℕ} (w : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    |w j| ≤ supNorm w := by
  unfold supNorm
  have := norm_le_pi_norm ((EuclideanSpace.equiv (Fin n) ℝ) w) j
  simpa [Real.norm_eq_abs] using this

theorem equations_18_19_core {n : ℕ} (g w : EuclideanSpace ℝ (Fin n))
    (ζ : ℝ) (hζ : ζ ^ 2 ≤ 1) :
    let η := Real.sqrt (1 - ζ ^ 2)
    let p₀ : Fin n → ℝ := fun j => (1 + ζ) * g j + η * w j
    let q₀ : Fin n → ℝ := fun j => (1 - ζ) * g j - η * w j
    (∀ j : Fin n,
      p₀ j * q₀ j = η ^ 2 * (g j) ^ 2 - 2 * ζ * η * g j * w j - η ^ 2 * (w j) ^ 2 ∧
      p₀ j * q₀ j = -(w j) ^ 2 + (η * g j - ζ * w j) ^ 2 ∧
      -(supNorm w) ^ 2 ≤ p₀ j * q₀ j) ∧
    negSupNorm (fun j => p₀ j * q₀ j) ≤ (supNorm w) ^ 2 := by
  intro η p₀ q₀
  have hη : η ^ 2 = 1 - ζ ^ 2 := Real.sq_sqrt (by linarith)
  have key : ∀ j, p₀ j * q₀ j = -(w j) ^ 2 + (η * g j - ζ * w j) ^ 2 := by
    intro j; simp only [p₀, q₀]; linear_combination (-g j ^ 2 - w j ^ 2) * hη
  have lb : ∀ j, -(supNorm w) ^ 2 ≤ p₀ j * q₀ j := by
    intro j
    rw [key j]
    have h1 := abs_le_supNorm_core w j
    have h2 : (w j) ^ 2 ≤ (supNorm w) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (η * g j - ζ * w j)]
  refine ⟨fun j => ⟨?_, key j, lb j⟩, ?_⟩
  · simp only [p₀, q₀]; linear_combination (-g j ^ 2) * hη
  · unfold negSupNorm
    refine (pi_norm_le_iff_of_nonneg (sq_nonneg _)).2 (fun j => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have := lb j
    constructor
    · have : min (p₀ j * q₀ j) 0 ≥ -(supNorm w)^2 := le_min this (by nlinarith [sq_nonneg (supNorm w)])
      linarith
    · have := min_le_right (p₀ j * q₀ j) 0
      nlinarith [sq_nonneg (supNorm w)]

end AdaptiveStepIPM.Probabilistic

open AdaptiveStepIPM.Probabilistic


theorem solution {n : ℕ} (g w : EuclideanSpace ℝ (Fin n))
    (ζ : ℝ) (hζ : ζ ^ 2 ≤ 1) :
    let η := Real.sqrt (1 - ζ ^ 2)
    let p₀ : Fin n → ℝ := fun j => (1 + ζ) * g j + η * w j
    let q₀ : Fin n → ℝ := fun j => (1 - ζ) * g j - η * w j
    (∀ j : Fin n,
      p₀ j * q₀ j = η ^ 2 * (g j) ^ 2 - 2 * ζ * η * g j * w j - η ^ 2 * (w j) ^ 2 ∧
      p₀ j * q₀ j = -(w j) ^ 2 + (η * g j - ζ * w j) ^ 2 ∧
      -(supNorm w) ^ 2 ≤ p₀ j * q₀ j) ∧
    negSupNorm (fun j => p₀ j * q₀ j) ≤ (supNorm w) ^ 2 := by
  exact equations_18_19_core g w ζ hζ
