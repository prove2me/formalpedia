-- Prove2me | Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F001
-- name    : LevyStochCalc_Ito_ItoFormulaShift_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:23:09.302352+00:00
-- url     : https://prove2.me/theorems/a1f40846-cd46-4a7d-b772-c30b516d223c
-- title:
--   Source declarations: LevyStochCalc.Ito.ItoFormulaShift
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.ItoFormulaShift. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaShift_F000
import Definitions.Def_SourceProof_700488d66fa58fc241f21293
import Definitions.Def_SourceProof_92457606fcd0d9dadd0bd79e

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a translated function

Translating the argument of a twice continuously differentiable function by a fixed vector
translates its Fréchet derivatives and its partial derivatives by the same vector, so Itô's
formula along a stopped path holds for the translate with every derivative read at the
translated path.

A weight that is known at a deterministic time and vanishes off the event that a stopping time
equals that time passes inside the Itô integral of an integrand that vanishes up to that
stopping time: the integrand is then carried by the window between that time and the horizon,
and the increment removed by the window is invisible on the event.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_shift` — Itô's formula along a stopped path for
  a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` — a bounded weight known at
  a deterministic time, cut to the event that a stopping time equals it, passes inside the Itô
  integral of an integrand vanishing up to that stopping time.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub` — the same for
  the increment of an integrand between two stopping times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Translate

variable {n : ℕ}

end Translate

section ShiftedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end ShiftedFormula

section StoppedIncrement

variable {Ω : Type u}

end StoppedIncrement

section HitIndPullOut

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The increment of an integrand between two stopping times carries a past weight inside the
Itô integral.** The weight is cut to the event that the earlier stopping time equals a
deterministic time and is otherwise known at that time. -/
theorem mul_stochasticIntegralBrownian_hitInd_stopped_sub
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hwm : Measurable (Function.uncurry fun ω s => hitInd σ a ω * V ω
      * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)))
    (hwp : Probability.ProgressivelyMeasurable ℱ fun ω s => hitInd σ a ω * V ω
      * (Probability.stopped τ K ω s - Probability.stopped σ K ω s))
    (hwq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω
        * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤) :
    (fun ω => hitInd σ a ω * V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ K ω s - Probability.stopped σ K ω s)
        ((Probability.measurable_uncurry_stopped hτ hmK).sub
          (Probability.measurable_uncurry_stopped hσ hmK))
        ((_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hτ hpK).sub
          (_root_.Prove2MeSourceProof.h_4014cddbf3dd1c22757fef9e hσ hpK))
        (_root_.Prove2MeSourceProof.h_700488d66fa58fc241f21293 (fun _ _ => sq_nnnorm_sub_le_two_mul _ _)
          (Probability.measurable_uncurry_stopped hτ hmK)
          (Probability.measurable_uncurry_stopped hσ hmK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK))
        T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω
          * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)) hwm hwp hwq T :=
  _root_.Prove2MeSourceProof.h_92457606fcd0d9dadd0bd79e W ℱ hℱ hσ ha haT hVb hVm hVa _ _ _
    (fun ω _ _ hs => stopped_sub_stopped_eq_zero hστ K ω hs) hwm hwp hwq
end HitIndPullOut

end LevyStochCalc.Brownian.Ito


