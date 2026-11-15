-- Prove2me | solution 1 for AppliedSDE.SarkkaSolin.girsanov_shifted_brownian_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:12:39.749365+00:00
-- url     : https://prove2.me/submissions/8ba40744-401e-4b94-ba5d-66517453400b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_pre_brownian_core
import Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_shifted_path_continuous_core
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionMaster
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Brownian
open scoped ENNReal NNReal Topology
set_option autoImplicit false
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
    IsBrownianReal shifted Q := by
  intro Q shifted
  exact {
    toIsPreBrownianReal :=
      AppliedSDE.SarkkaSolin.girsanov_shifted_pre_brownian_core
        P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean
    cont :=
      AppliedSDE.SarkkaSolin.girsanov_shifted_path_continuous_core
        P W ℱ hW T hT θ hθmeas hθprog hθq hθzero Z hZ hZmean
  }
