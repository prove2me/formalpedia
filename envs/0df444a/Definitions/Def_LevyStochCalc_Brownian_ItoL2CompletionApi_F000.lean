-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionApi_F000
-- name    : LevyStochCalc_Brownian_ItoL2CompletionApi_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:34:24.482075+00:00
-- url     : https://prove2.me/theorems/24843d54-5ca9-43cc-95ca-d9910ea2b73f
-- title:
--   Source declarations: LevyStochCalc.Brownian.ItoL2CompletionApi
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.ItoL2CompletionApi. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- **Unified L²-Itô integral with martingale + quadVar + isometry** (formerly cited
axiom #5, now a theorem).

For predictable square-integrable `H : Ω → ℝ → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t H² ds` is a martingale wrt `Filt` (quadVar identity),
* `∫⁻ ω, ‖F T‖₊² ∂P = ∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P`
  for every `T > 0`
  (L²-isometry).

The statement asserts existence of *some* process `F` with these three
properties for `Filt = ℱ.rightCont`; it does not name `F` or mention `W`. The
witness supplied by the proof is `stochasticIntegralBrownian`; the pinned
forms that name it directly are `isometry_stochasticIntegralBrownian`,
`martingale_rightCont_stochasticIntegralBrownian` and
`itoIsometry_diff_brownian`. The 3-conjunct strong existence consolidates
Karatzas–Shreve Thm 3.2.6.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** (unified martingale + quadratic variation +
L²-isometry of the L² Itô integral); Le Gall, J.-F. *Brownian Motion, Martingales
and Stochastic Calculus*, Springer 2016, **Theorem 5.4** + equation **(5.8)**.

**Construction**: `F := stochasticIntegralBrownian` is the coherent `L²`-limit of the
`masterApprox` simple integrals across growing horizons. Conjunct 1
(`martingale_rightCont_stochasticIntegralBrownian`) and conjunct 3
(`isometry_stochasticIntegralBrownian`) were proven directly; conjunct 2
(`martingale_rightCont_quadVar_stochasticIntegralBrownian`) is the set-level Itô
isometry at simple level lifted through the `L¹`-limit of the compensated squares and
the `rightCont` right-`L¹`-continuity. `Filt` is pinned to
`ℱ.rightCont`. -/
theorem itoIsometry_brownian_unified_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = ℱ.rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      (∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
  ⟨stochasticIntegralBrownian W ℱ hℱ H h_meas h_progMeas h_sq_int_global,
    ℱ.rightCont, rfl,
    _root_.Prove2MeSourceProof.h_08c64b3622d7f10f8c921d88 W ℱ hℱ H h_meas h_progMeas h_sq_int_global,
    _root_.Prove2MeSourceProof.h_580018e2ba31f91ba73e0981 W ℱ hℱ H h_meas h_progMeas
      h_sq_int_global,
    fun _ hT => _root_.Prove2MeSourceProof.h_7aea30f549f53f05062f1907 W ℱ hℱ H h_meas h_progMeas h_sq_int_global hT⟩
end LevyStochCalc.Brownian.Ito


