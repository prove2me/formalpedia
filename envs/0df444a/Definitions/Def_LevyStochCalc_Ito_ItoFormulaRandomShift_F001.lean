-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
-- name    : LevyStochCalc_Ito_ItoFormulaRandomShift_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:39:37.986952+00:00
-- url     : https://prove2.me/theorems/fffd482d-57b9-467d-b6c3-873f5afd17b0
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaRandomShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaRandomShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Passing to the limit in a shifted Itô formula

A shift of the argument of a `C²` function by a random vector is approximated by shifts along a
sequence of random vectors converging to it pointwise. Each term of the resulting identity
converges: the boundary term by continuity of the function, the two Lebesgue terms by dominated
convergence along the path, and the stochastic term in `L²` by the difference isometry, hence
almost surely along a subsequence. An identity holding for every member of the sequence therefore
holds in the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.stopped_sub` — cutting off at a stopping time is linear.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` — the energy of the difference of
  two shifted integrands vanishes along a pointwise-convergent sequence of shifts.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_of_forall_ae_eq` — an almost-everywhere identity
  survives an almost-everywhere limit on both sides.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy` — a vanishing
  energy distance between integrands gives a vanishing `L²` distance between their Itô integrals.
* `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` — the same over
  finitely many Brownian channels, almost surely along a common subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {α : Type*}

section StoppedAlgebra

variable {Ω : Type*}

end StoppedAlgebra

section LimitTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end LimitTransfer

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section PathIntegral

variable {Ω : Type u}

end PathIntegral

section StochasticTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- A vanishing energy distance between integrands gives a vanishing `L²` distance between their
Itô integrals. -/
theorem tendsto_lintegral_sq_stochInt_of_tendsto_energy
    (G : ℕ → Ω → ℝ → ℝ) (G₀ : Ω → ℝ → ℝ)
    (hmG : ∀ m, Measurable (Function.uncurry (G m)))
    (hpG : ∀ m, Probability.ProgressivelyMeasurable ℱ (G m))
    (hqG : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmG₀ : Measurable (Function.uncurry G₀))
    (hpG₀ : Probability.ProgressivelyMeasurable ℱ G₀)
    (hqG₀ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hE : Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G m ω s - G₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∫⁻ ω,
        (‖stochasticIntegralBrownian W ℱ hℱ (G m) (hmG m) (hpG m) (hqG m) T ω
          - stochasticIntegralBrownian W ℱ hℱ G₀ hmG₀ hpG₀ hqG₀ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) :=
  hE.congr fun m => (_root_.Prove2MeSourceProof.h_9ab1096355abba8f677466b8 W ℱ hℱ (G m) G₀
    (hmG m) hmG₀ (hpG m) hpG₀ (hqG m) hqG₀ hT).symm
end StochasticTerm

section MultiChannel

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end MultiChannel

end LevyStochCalc.Brownian.Ito


