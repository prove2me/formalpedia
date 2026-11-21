-- Prove2me | Definitions.Def_SourceProof_ea708e0a6ffe599032f388e2
-- name    : SourceProof_ea708e0a6ffe599032f388e2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:26:59.074877+00:00
-- url     : https://prove2.me/theorems/6e95ef1d-49dc-4449-9dbf-b3d52c0dd1e0
-- title:
--   LevyStochCalc source module: SourceProof_ea708e0a6ffe599032f388e2
-- statement:
--   The original source theorem `LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegralBrownian` comes from the `LevyStochCalc.Ito.SecondMomentToolkit` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_SecondMomentToolkit_F003
import Definitions.Def_SourceProof_9ab1096355abba8f677466b8

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

variable {b T}

end Running

section Polarised


theorem _root_.Prove2MeSourceProof.h_ea708e0a6ffe599032f388e2 (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, H ω s * K ω s ∂volume ∂P := by
  have hU2 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hHm hHp hHs T
  have hV2 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ K hKm hKp hKs T
  have hUV2 : MemLp (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) 2 P :=
    hU2.sub hV2
  have hdiff := _root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ H K
    hHm hKm hHp hKp hHs hKs hT
  have hdq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    rw [← hdiff]
    exact LevyStochCalc.Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hUV2
  have hHm2 := LevyStochCalc.Ito.SecondMoment.memLp_two_prod hHm (hHs T hT)
  have hKm2 := LevyStochCalc.Ito.SecondMoment.memLp_two_prod hKm (hKs T hT)
  -- the three energies, on the product measure
  have hUU : ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω ∂P
      = ∫ p, H p.1 p.2 * H p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hU2,
      _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H hHm hHp hHs hT]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_eq hHm (hHs T hT)
  have hVV : ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω ∂P
      = ∫ p, K p.1 p.2 * K p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hV2,
      _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ K hKm hKp hKs hT]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_eq hKm (hKs T hT)
  have hDD : ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) ∂P
      = ∫ p, (H p.1 p.2 - K p.1 p.2) * (H p.1 p.2 - K p.1 p.2)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_toReal hUV2, hdiff]
    exact LevyStochCalc.Ito.SecondMoment.toReal_lintegral_sq_eq (f := fun ω s => H ω s - K ω s) (hHm.sub hKm) hdq
  -- the algebra of the polarisation identity
  have iUU : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω) P :=
    hU2.integrable_mul hU2
  have iVV : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) P :=
    hV2.integrable_mul hV2
  have iDD : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
      * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)) P :=
    hUV2.integrable_mul hUV2
  have iS : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
      + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) P :=
    iUU.add iVV
  have hexp : (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
      = fun ω =>
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        - (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω))
        / 2 := by
    funext ω
    ring
  have iHH : Integrable (fun p : Ω × ℝ => H p.1 p.2 * H p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hHm2.integrable_mul hHm2
  have iKK : Integrable (fun p : Ω × ℝ => K p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hKm2.integrable_mul hKm2
  have iHK : Integrable (fun p : Ω × ℝ => H p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hHm2.integrable_mul hKm2
  have iDD' : Integrable (fun p : Ω × ℝ => (H p.1 p.2 - K p.1 p.2) * (H p.1 p.2 - K p.1 p.2))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (hHm2.sub hKm2).integrable_mul (hHm2.sub hKm2)
  have iS' : Integrable (fun p : Ω × ℝ => H p.1 p.2 * H p.1 p.2 + K p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := iHH.add iKK
  rw [hexp, integral_div, integral_sub iS iDD, integral_add iUU iVV, hUU, hVV, hDD,
    ← integral_add iHH iKK, ← integral_sub iS' iDD', ← integral_div, ← integral_prod _ iHK]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring
end Polarised

section PolarisedDrift

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment


