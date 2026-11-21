-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F002
-- name    : LevyStochCalc_Brownian_ItoL2CompletionApi_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:34:14.623178+00:00
-- url     : https://prove2.me/theorems/86ebb136-19b9-439a-9323-2c8077049b34
-- title:
--   LevyStochCalc source module: LevyStochCalc.Brownian.ItoL2CompletionApi
-- statement:
--   Exact source-faithful declarations from LevyStochCalc.Brownian.ItoL2CompletionApi in the pinned LevyStochCalc project.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionQuadVar_F002
import Definitions.Def_SourceProof_08c64b3622d7f10f8c921d88
import Definitions.Def_SourceProof_580018e2ba31f91ba73e0981
import Definitions.Def_SourceProof_7aea30f549f53f05062f1907

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Brownian Itô integral: the `stochasticIntegral` API

The martingale property of the compensated square for the right-continuation `ℱ₊` of `ℱ`,
the unified existence theorem `itoIsometry_brownian_unified_existence` combining the
martingale, quadratic-variation and isometry conclusions, the isometry for differences of
integrands, and the `stochasticIntegral` interface with `itoIsometry`,
`quadVar_stochasticIntegral` and `martingale_stochasticIntegral`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

end MasterSequence

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

The **constructed** L²-limit process `stochasticIntegralBrownian` (the coherent
`L²`-limit of the `masterApprox` simple integrals), not a `Classical.choose`
witness — so it is genuinely linear-friendly (used by `itoIsometry_diff_brownian`). -/
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global T
/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form.

Forwards to the L²-isometry conjunct of `itoIsometry_brownian_unified_existence`. -/
theorem itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT
/-- **Quadratic variation of the L² Itô integral.**

For predictable square-integrable `H`, the process `t ↦ (M_t)² − ∫_0^t |H_s|² ds`,
where `M_t = ∫_0^t H_s dW_s`, is a martingale with respect to some filtration
(the statement does not name it; the pinned form for `ℱ.rightCont` is
`martingale_rightCont_quadVar_stochasticIntegralBrownian`).

Extracts conjunct 2 (quadratic variation) of `itoIsometry_brownian_unified_existence`. -/
theorem quadVar_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2)
        F P := by
  unfold stochasticIntegral
  exact ⟨ℱ.rightCont,
    _root_.Prove2MeSourceProof.h_580018e2ba31f91ba73e0981 W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global⟩
/-- **The L² Itô integral is a martingale.**

The Itô integral `M_t = ∫_0^t H_s dW_s` is a martingale with respect to some
filtration (the statement does not name it; the pinned form for `ℱ.rightCont`
is `martingale_rightCont_stochasticIntegralBrownian`).

Extracts conjunct 1 (martingale property) of `itoIsometry_brownian_unified_existence`. -/
theorem martingale_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq_int_global t) F P := by
  unfold stochasticIntegral
  exact ⟨ℱ.rightCont,
    _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H h_meas h_progMeas h_sq_int_global⟩
end LevyStochCalc.Brownian.Ito


