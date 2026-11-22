-- Prove2me | Definitions.Def_SourceProof_e6dcd6270ba2ccc8443bc922
-- name    : SourceProof_e6dcd6270ba2ccc8443bc922
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T07:46:39.560878+00:00
-- url     : https://prove2.me/theorems/a1e726b8-c871-494b-8887-68ad88bb9d7f
-- title:
--   LevyStochCalc source module: SourceProof_e6dcd6270ba2ccc8443bc922
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` comes from the `LevyStochCalc.Ito.ItoFormulaRandomShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_SourceProof_7c1e051c1c1f9aebd6c80fa9

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

end StochasticTerm

section MultiChannel

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


theorem _root_.Prove2MeSourceProof.h_e6dcd6270ba2ccc8443bc922 {ι : Type*} [Finite ι]
    (W : ι → LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W i) ℱ)
    (G : ℕ → ι → Ω → ℝ → ℝ) (G₀ : ι → Ω → ℝ → ℝ)
    (hmG : ∀ m i, Measurable (Function.uncurry (G m i)))
    (hpG : ∀ m i, Probability.ProgressivelyMeasurable ℱ (G m i))
    (hqG : ∀ (m : ℕ) (i : ι) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G m i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmG₀ : ∀ i, Measurable (Function.uncurry (G₀ i)))
    (hpG₀ : ∀ i, Probability.ProgressivelyMeasurable ℱ (G₀ i))
    (hqG₀ : ∀ (i : ι) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G₀ i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hE : ∀ i, Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G m i ω s - G₀ i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (nhds 0)) :
    ∃ ms : ℕ → ℕ, (∀ m : ℕ, m ≤ ms m) ∧ ∀ᵐ ω ∂P, ∀ i : ι, Filter.Tendsto
      (fun m => stochasticIntegralBrownian (W i) ℱ (hℱ i) (G (ms m) i)
        (hmG (ms m) i) (hpG (ms m) i) (hqG (ms m) i) T ω)
      Filter.atTop (nhds (stochasticIntegralBrownian (W i) ℱ (hℱ i) (G₀ i)
        (hmG₀ i) (hpG₀ i) (hqG₀ i) T ω)) := by
  letI : Fintype ι := Fintype.ofFinite ι
  refine _root_.Prove2MeSourceProof.h_7c1e051c1c1f9aebd6c80fa9 (μ := P) (ι := ι)
    (u := fun m i ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W i) ℱ (hℱ i) (G m i)
      (hmG m i) (hpG m i) (hqG m i) T ω)
    (v := fun i ω => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W i) ℱ (hℱ i) (G₀ i)
      (hmG₀ i) (hpG₀ i) (hqG₀ i) T ω)
    (fun m i => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W i) ℱ (hℱ i) _
      (hmG m i) (hpG m i) (hqG m i) T).mono (ℱ.le T)).measurable)
    (fun i => ((LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stronglyAdapted (W i) ℱ (hℱ i) _
      (hmG₀ i) (hpG₀ i) (hqG₀ i) T).mono (ℱ.le T)).measurable)
    fun i => LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy (W i) ℱ (hℱ i)
      (fun m => G m i) (G₀ i) (fun m => hmG m i) (fun m => hpG m i) (fun m => hqG m i)
      (hmG₀ i) (hpG₀ i) (hqG₀ i) hT (hE i)
end MultiChannel

end LevyStochCalc.Brownian.Ito


