-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:49:21.061225+00:00
-- url     : https://prove2.me/submissions/34a581ab-3442-463b-8ff1-693ef9948bb0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AppliedSDE_SarkkaSolin_unit_mean_density_is_probability
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_brownian_core
set_option autoImplicit false
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hW : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (T : ℝ) (hT : 0 < T)
    (θ : Ω → ℝ → ℝ)
    (hθmeas : Measurable (Function.uncurry θ))
    (hθprog : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ θ)
    (hθq : ∀ (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖θ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hθzero : ∀ (ω : Ω) (s : ℝ), T ≤ s → θ ω s = 0)
    (Z : Ω → ℝ)
    (hZ : ∀ ω : Ω,
      Z ω = Real.exp (
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hW θ hθmeas hθprog hθq T ω -
        (1 / 2 : ℝ) * ∫ s in (0 : ℝ)..T, θ ω s ^ 2))
    (hZmean : ∫ ω, Z ω ∂P = 1) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q := by
  dsimp only
  have hZnonneg (ω : Ω) : 0 ≤ Z ω := by
    rw [hZ ω]
    positivity
  have hZint : Integrable Z P := by
    by_contra hnot
    have hzero : (∫ ω, Z ω ∂P) = 0 := integral_undef hnot
    rw [hZmean] at hzero
    norm_num at hzero
  constructor
  · exact AppliedSDE.SarkkaSolin.unit_mean_density_is_probability
      P Z hZint hZnonneg hZmean
  · exact AppliedSDE.SarkkaSolin.girsanov_shifted_brownian_core
      P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean
