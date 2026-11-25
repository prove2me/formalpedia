-- Prove2me | solution 1 for Arxiv0812_1178.cartesian_moments_scalar_case
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T17:34:04.304388+00:00
-- url     : https://prove2.me/submissions/f054e4b7-6b6b-492c-bc78-f31e26d0eeb0

import Mathlib
import Definitions.Def_Arxiv0812_1178_Basic
import Theorems.Thm_Arxiv0812_1178_cartesian_moments_polar_gaussian

open MeasureTheory ProbabilityTheory Matrix Arxiv0812_1178

theorem solution {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr] (abar phibar : ι → ℝ)
    (σa σφ : ι → ℝ)
    (anoise phinoise : Ω → EuclideanSpace ℝ ι) (ham : Measurable anoise)
    (hφm : Measurable phinoise)
    (hag : Pr.map anoise = multivariateGaussian 0 (Matrix.diagonal fun i => σa i ^ 2))
    (hφg : Pr.map phinoise = multivariateGaussian 0 (Matrix.diagonal fun i => σφ i ^ 2))
    (hind : IndepFun anoise phinoise Pr) :
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      if i = j then
        abar i ^ 2 / 2 * (1 - Real.exp (-(σφ i ^ 2))) ^ 2 +
          σa i ^ 2 / 2 * (1 + Real.exp (-(2 * σφ i ^ 2)))
      else 0) ∧
    (∀ i j, covariance
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr =
      if i = j then
        abar i ^ 2 / 2 * (1 - Real.exp (-(2 * σφ i ^ 2))) +
          σa i ^ 2 / 2 * (1 - Real.exp (-(2 * σφ i ^ 2)))
      else 0) ∧
    (∀ i j, covariance
        (fun ω => radNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) i)
        (fun ω => tanNoise abar phibar (fun k => anoise ω k) (fun k => phinoise ω k) j) Pr = 0) := by
  have hRa : (Matrix.diagonal fun i => σa i ^ 2).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sq_nonneg (σa i)
  have hRφ : (Matrix.diagonal fun i => σφ i ^ 2).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => sq_nonneg (σφ i)
  have hM := cartesian_moments_polar_gaussian Pr abar phibar _ _ hRa hRφ anoise phinoise
    ham hφm hag hφg hind
  refine ⟨?_, ?_, hM.2.2.2.1⟩
  · intro i j
    rw [hM.2.2.1 i j]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Matrix.diagonal_apply_eq]
      have h1 : -((σφ i ^ 2 + σφ i ^ 2) / 2) = -(σφ i ^ 2) := by ring
      rw [h1, Real.cosh_eq]
      have h2 : Real.exp (σφ i ^ 2) * Real.exp (-(σφ i ^ 2)) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2)) = Real.exp (-(2 * σφ i ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexp :
          (abar i * abar i * ((Real.exp (σφ i ^ 2) + Real.exp (-(σφ i ^ 2))) / 2 - 1) +
            σa i ^ 2 * ((Real.exp (σφ i ^ 2) + Real.exp (-(σφ i ^ 2))) / 2)) *
            Real.exp (-(σφ i ^ 2)) =
          abar i ^ 2 / 2 * (Real.exp (σφ i ^ 2) * Real.exp (-(σφ i ^ 2)) -
            2 * Real.exp (-(σφ i ^ 2)) +
            Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2))) +
          σa i ^ 2 / 2 * (Real.exp (σφ i ^ 2) * Real.exp (-(σφ i ^ 2)) +
            Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2))) := by ring
      rw [hexp, h2, h3]
      have hsq : (1 - Real.exp (-(σφ i ^ 2))) ^ 2 =
          1 - 2 * Real.exp (-(σφ i ^ 2)) + Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2)) := by ring
      rw [hsq, h3]
    · simp only [hij, ↓reduceIte, Matrix.diagonal_apply_ne _ hij, Real.cosh_zero, sub_self,
        mul_zero, add_zero, zero_mul]
  · intro i j
    rw [hM.2.2.2.2 i j]
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte, Matrix.diagonal_apply_eq]
      have h1 : -((σφ i ^ 2 + σφ i ^ 2) / 2) = -(σφ i ^ 2) := by ring
      rw [h1, Real.sinh_eq]
      have h2 : Real.exp (σφ i ^ 2) * Real.exp (-(σφ i ^ 2)) = 1 := by
        rw [← Real.exp_add]; simp
      have h3 : Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2)) = Real.exp (-(2 * σφ i ^ 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hexp :
          (abar i * abar i + σa i ^ 2) *
            ((Real.exp (σφ i ^ 2) - Real.exp (-(σφ i ^ 2))) / 2) * Real.exp (-(σφ i ^ 2)) =
          (abar i ^ 2 / 2 + σa i ^ 2 / 2) *
            (Real.exp (σφ i ^ 2) * Real.exp (-(σφ i ^ 2)) -
              Real.exp (-(σφ i ^ 2)) * Real.exp (-(σφ i ^ 2))) := by ring
      rw [hexp, h2, h3]
      ring
    · simp only [hij, ↓reduceIte, Matrix.diagonal_apply_ne _ hij, Real.sinh_zero, mul_zero, zero_mul]
