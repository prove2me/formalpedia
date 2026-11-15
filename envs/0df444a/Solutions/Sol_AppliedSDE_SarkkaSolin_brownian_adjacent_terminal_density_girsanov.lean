-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.brownian_adjacent_terminal_density_girsanov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:20:51.705741+00:00
-- url     : https://prove2.me/submissions/cdf3b141-cef1-4f63-9ef0-860509abb074

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increment_esscher_tilt
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r < s) (hst : s < t) (theta : ℝ) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (theta * (W.W (t : ℝ) ω - W.W (r : ℝ) ω) -
        ((t - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
      (fun ω => (W.W (s : ℝ) ω - W.W (r : ℝ) ω,
        W.W (t : ℝ) ω - W.W (s : ℝ) ω)) =
      (gaussianReal (((s - r : ℝ≥0) : ℝ) * theta) (s - r)).prod
        (gaussianReal (((t - s : ℝ≥0) : ℝ) * theta) (t - s)) := by
  let X : Ω → ℝ := fun ω => W.W (s : ℝ) ω - W.W (r : ℝ) ω
  let Y : Ω → ℝ := fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω
  have hfactor : ∀ ω : Ω,
      ENNReal.ofReal
        (Real.exp (theta * (W.W (t : ℝ) ω - W.W (r : ℝ) ω) -
          ((t - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) =
      ENNReal.ofReal
        (Real.exp (theta * X ω - ((s - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) *
      ENNReal.ofReal
        (Real.exp (theta * Y ω - ((t - s : ℝ≥0) : ℝ) * theta ^ 2 / 2)) := by
    intro ω
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    rw [← Real.exp_add]
    congr 1
    simp only [NNReal.coe_sub (le_trans hrs.le hst.le),
      NNReal.coe_sub hrs.le, NNReal.coe_sub hst.le]
    dsimp [X, Y]
    ring
  have hQ :
      P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (theta * (W.W (t : ℝ) ω - W.W (r : ℝ) ω) -
          ((t - r : ℝ≥0) : ℝ) * theta ^ 2 / 2))) =
      P.withDensity (fun ω =>
        ENNReal.ofReal
          (Real.exp (theta * X ω - ((s - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * Y ω - ((t - s : ℝ≥0) : ℝ) * theta ^ 2 / 2))) := by
    congr 1
    funext ω
    exact hfactor ω
  change (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (theta * (W.W (t : ℝ) ω - W.W (r : ℝ) ω) -
        ((t - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
      (fun ω => (X ω, Y ω)) = _
  rw [hQ]
  exact AppliedSDE.SarkkaSolin.brownian_adjacent_increment_esscher_tilt
    W r s t hrs hst theta
