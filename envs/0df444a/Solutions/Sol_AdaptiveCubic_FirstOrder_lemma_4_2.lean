-- Prove2me | solution 1 for AdaptiveCubic.FirstOrder.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T10:58:16.170639+00:00
-- url     : https://prove2.me/submissions/cb68610b-fd76-48ec-8be8-021f4a07fdd1

import Mathlib
import Definitions.Def_AdaptiveCubic_Cauchy_model

set_option autoImplicit false
open scoped RealInnerProductSpace

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (σ : ℝ) (x sk : EuclideanSpace ℝ (Fin n))
    (h41 : ⟪gradient f x, sk⟫ + ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3 = 0)
    (h42 : 0 ≤ ⟪sk, B sk⟫ + σ * ‖sk‖ ^ 3) :
    1 / 6 * σ * ‖sk‖ ^ 3 ≤ f x - AdaptiveCubic.Cauchy.model f B σ x sk := by
  unfold AdaptiveCubic.Cauchy.model
  rw [real_inner_comm sk (gradient f x)] at h41
  nlinarith [h41, h42]
