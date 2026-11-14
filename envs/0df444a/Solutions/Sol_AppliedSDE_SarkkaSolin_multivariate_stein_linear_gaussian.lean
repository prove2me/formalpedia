-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.multivariate_stein_linear_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:01:31.171201+00:00
-- url     : https://prove2.me/submissions/4e36b77b-c39f-402d-9ea7-70f25618329f

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_stein_affine_coordinate
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators

theorem solution
    {n m : ℕ}
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (μ : Fin n → ℝ)
    (f : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (t : ℝ)
    (hf : ∀ i : Fin n, ContDiff ℝ 1 (fun x : Fin n → ℝ => f t x i))
    (hfb : ∃ C : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n), |f t x i| ≤ C)
    (hfdb : ∃ D : ℝ, ∀ (x : Fin n → ℝ) (i : Fin n),
      ‖fderiv ℝ (fun y : Fin n → ℝ => f t y i) x‖ ≤ D)
    (i j : Fin n) :
    (∫ z : Fin m → ℝ, f t (μ + L z) i * (L z) j
      ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) =
      ∑ k : Fin m, (L (Pi.single k (1 : ℝ))) j *
        (∫ z : Fin m → ℝ,
          fderiv ℝ (fun y : Fin n → ℝ => f t y i) (μ + L z)
            (L (Pi.single k (1 : ℝ)))
          ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1))) := by
  classical
  rcases hfb with ⟨C, hC⟩
  rcases hfdb with ⟨D, hD⟩
  cases m with
  | zero =>
      have hz (z : Fin 0 → ℝ) : L z = 0 := by
        have h : z = 0 := Subsingleton.elim _ _
        rw [h]
        exact L.map_zero
      simp [hz]
  | succ m =>
      let γ : Measure (Fin (m + 1) → ℝ) :=
        Measure.pi (fun _ : Fin (m + 1) => gaussianReal 0 1)
      let g : (Fin n → ℝ) → ℝ := fun x => f t (μ + x) i
      have hg : ContDiff ℝ 1 g := (hf i).comp (contDiff_const.add contDiff_id)
      have hstein (k : Fin (m + 1)) :
          (∫ z : Fin (m + 1) → ℝ, z k * g (L z) ∂γ) =
          ∫ z : Fin (m + 1) → ℝ,
            fderiv ℝ (fun y : Fin n → ℝ => f t y i)
              (μ + L z) (L (Pi.single k (1 : ℝ))) ∂γ := by
        simpa only [g, γ] using
          (AppliedSDE.SarkkaSolin.gaussian_stein_affine_coordinate
            L μ (fun y : Fin n → ℝ => f t y i) (hf i)
            ⟨C, fun x => hC x i⟩ ⟨D, fun x => hD x i⟩ k)
      have hz (k : Fin (m + 1)) :
          Integrable (fun z : Fin (m + 1) → ℝ => z k) γ := by
        simpa only [γ] using (integrable_eval IsGaussian.integrable_id
          (i := k))
      have hgg : AEStronglyMeasurable
          (fun z : Fin (m + 1) → ℝ => g (L z)) γ :=
        (hg.continuous.comp L.continuous).aestronglyMeasurable
      have hprod (k : Fin (m + 1)) :
          Integrable (fun z : Fin (m + 1) → ℝ => z k * g (L z)) γ := by
        apply (hz k).mul_bdd hgg
        filter_upwards [] with z
        simpa only [g, Real.norm_eq_abs] using hC (μ + L z) i
      have hvec (z : Fin (m + 1) → ℝ) :
          z = ∑ k : Fin (m + 1), z k • Pi.single k (1 : ℝ) := by
        ext ell
        simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
      have hL (z : Fin (m + 1) → ℝ) :
          (L z) j = ∑ k : Fin (m + 1),
            z k * (L (Pi.single k (1 : ℝ))) j := by
        conv_lhs => rw [hvec z]
        simp [map_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have hinterm (z : Fin (m + 1) → ℝ) :
          f t (μ + L z) i * (L z) j =
            ∑ k : Fin (m + 1),
              (L (Pi.single k (1 : ℝ))) j * (z k * g (L z)) := by
        rw [hL z, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp [g]
        ring
      change (∫ z : Fin (m + 1) → ℝ,
          f t (μ + L z) i * (L z) j ∂γ) =
        ∑ k : Fin (m + 1), (L (Pi.single k (1 : ℝ))) j *
          (∫ z : Fin (m + 1) → ℝ,
            fderiv ℝ (fun y : Fin n → ℝ => f t y i) (μ + L z)
              (L (Pi.single k (1 : ℝ))) ∂γ)
      calc
        (∫ z : Fin (m + 1) → ℝ,
          f t (μ + L z) i * (L z) j ∂γ) =
            ∫ z : Fin (m + 1) → ℝ,
              ∑ k : Fin (m + 1),
                (L (Pi.single k (1 : ℝ))) j *
                  (z k * g (L z)) ∂γ := by
                    apply integral_congr_ae
                    filter_upwards [] with z
                    exact hinterm z
        _ = ∑ k : Fin (m + 1), ∫ z : Fin (m + 1) → ℝ,
              (L (Pi.single k (1 : ℝ))) j *
                  (z k * g (L z)) ∂γ := by
                    rw [integral_finset_sum]
                    exact fun k _ => (hprod k).const_mul _
        _ = ∑ k : Fin (m + 1), (L (Pi.single k (1 : ℝ))) j *
              (∫ z : Fin (m + 1) → ℝ, z k * g (L z) ∂γ) := by
                simp_rw [integral_const_mul]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hstein k]
