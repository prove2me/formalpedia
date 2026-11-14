-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.gaussian_stein_affine_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:42:41.496345+00:00
-- url     : https://prove2.me/submissions/adf054a9-2f08-43b6-8ab2-43b3860c24d4

import Mathlib
import Theorems.Thm_HighDimProb_RandomProcesses_gaussian_linear_integration_by_parts
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem solution
    {n m : ℕ}
    (L : (Fin (m + 1) → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ : Fin n → ℝ) (g : (Fin n → ℝ) → ℝ)
    (hg : ContDiff ℝ 1 g)
    (hgb : ∃ C : ℝ, ∀ x : Fin n → ℝ, |g x| ≤ C)
    (hgdb : ∃ D : ℝ, ∀ x : Fin n → ℝ, ‖fderiv ℝ g x‖ ≤ D)
    (k : Fin (m + 1)) :
    (∫ z : Fin (m + 1) → ℝ, z k * g (μ + L z)
      ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))) =
    ∫ z : Fin (m + 1) → ℝ,
      fderiv ℝ g (μ + L z) (L (Pi.single k (1 : ℝ)))
      ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1)) := by
  rcases hgb with ⟨C, hC⟩
  rcases hgdb with ⟨D, hD⟩
  let G : (Fin n → ℝ) → ℝ := fun x => g (μ + x)
  have hshift : ContDiff ℝ 1 (fun x : Fin n → ℝ => μ + x) :=
    contDiff_const.add contDiff_id
  have hG : ContDiff ℝ 1 G := hg.comp hshift
  have hGb (x : Fin n → ℝ) : ‖G x‖ ≤ C := by
    simpa only [G, Real.norm_eq_abs] using hC (μ + x)
  have hGderiv (x : Fin n → ℝ) :
      fderiv ℝ G x = fderiv ℝ g (μ + x) := by
    exact fderiv_comp_add_left (𝕜 := ℝ) (f := g) (x := x) μ
  have hGdb (x : Fin n → ℝ) :
      ‖fderiv ℝ G x‖ ≤ D := by
    rw [hGderiv x]
    exact hD (μ + x)
  have hstein :=
    HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts
      L k G hG hGb hGdb
  calc
    (∫ z : Fin (m + 1) → ℝ, z k * g (μ + L z)
      ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1))) =
        ∫ z : Fin (m + 1) → ℝ, z k * G (L z)
          ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1)) := rfl
    _ = ∫ z : Fin (m + 1) → ℝ,
          fderiv ℝ G (L z) (L (Pi.single k (1 : ℝ)))
          ∂(Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1)) := hstein.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hGderiv]