-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_brownian_shift_of_novikov
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:37:10.865442+00:00
-- url     : https://prove2.me/submissions/87bdcb9c-bcf8-48da-89d0-fcdc34f46d01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
import Theorems.Thm_AppliedSDE_SarkkaSolin_novikov_stochastic_exponential_unit_mean
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_brownian_shift_terminal_density
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
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
    (hNovikov : Integrable (fun ω : Ω =>
      Real.exp ((1 / 2 : ℝ) *
        ∫ s in (0 : ℝ)..T, θ ω s ^ 2)) P) :
    let Q : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal (Z ω))
    let shifted : ℝ≥0 → Ω → ℝ := fun t ω =>
      W.W (t : ℝ) ω - ∫ s in (0 : ℝ)..(t : ℝ), θ ω s
    (∫ ω, Z ω ∂P = 1) ∧
      IsProbabilityMeasure Q ∧ IsBrownianReal shifted Q := by
  dsimp only
  have hm : (∫ ω, Z ω ∂P) = 1 :=
    AppliedSDE.SarkkaSolin.novikov_stochastic_exponential_unit_mean
      P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hNovikov
  constructor
  · exact hm
  · exact AppliedSDE.SarkkaSolin.girsanov_brownian_shift_terminal_density
      P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hm
