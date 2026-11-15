-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.euler_integrated_lipschitz_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:10:12.426001+00:00
-- url     : https://prove2.me/submissions/5c108702-d4da-4a55-8b30-5116d05b5fb5

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AppliedSDE_SarkkaSolin_euler_lipschitz_squared_sum
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X Y : Ω → ℝ) (b σ : ℝ → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hb : ∀ x y : ℝ, |b x - b y| ≤ L * |x - y|)
    (hσ : ∀ x y : ℝ, |σ x - σ y| ≤ L * |x - y|)
    (hi : Integrable
      (fun ω => (b (X ω) - b (Y ω)) ^ 2 +
        (σ (X ω) - σ (Y ω)) ^ 2) P)
    (hj : Integrable
      (fun ω => (2 * L ^ 2) * (X ω - Y ω) ^ 2) P) :
    (∫ ω, ((b (X ω) - b (Y ω)) ^ 2 +
      (σ (X ω) - σ (Y ω)) ^ 2) ∂P) ≤
      ∫ ω, (2 * L ^ 2) * (X ω - Y ω) ^ 2 ∂P := by
  apply integral_mono_ae hi hj
  filter_upwards [] with ω
  simpa only [sq_abs] using
    (AppliedSDE.SarkkaSolin.euler_lipschitz_squared_sum
      b σ L hL hb hσ (X ω) (Y ω))
