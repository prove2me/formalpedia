-- Prove2me | Definitions.Def_SourceProof_6839e78f61d86c5ab0f11397
-- name    : SourceProof_6839e78f61d86c5ab0f11397
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T16:31:32.820099+00:00
-- url     : https://prove2.me/theorems/03496521-91e0-4c7e-a2d9-5b095cbe1c9b
-- title:
--   LevyStochCalc source module: SourceProof_6839e78f61d86c5ab0f11397
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_incr_sq` comes from the `LevyStochCalc.Poisson.MarkStepIncrement` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_5608c3a7eb7b3d3f0d0b6fe4
import Definitions.Def_SourceProof_674b57f2d7b8e4e407676e25

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Dyadic mark-step integrands and their weighted increments

On the dyadic grids `TimeGrid.dyadic T hT n` of `[0, T]`, a mark-step integrand of level
`n` is re-expressed on any finer level `m ≥ n` (`MarkStep.dyadicRefine`), each fine piece
inheriting the coefficients of the coarse piece containing it, and is restricted to a
horizon `T'` with `T = T' * 2 ^ d` (`MarkStep.dyadicRestrict`); both leave the compensated
integral and the integrand unchanged. The increment of a mark-step integrand over `(s, t]`,
weighted by a bounded measurable `w`, is itself a mark-step integrand on the increment grid
`TimeGrid.incr` (`MarkStep.incr`), which gives the `L²` isometry for such increments.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

end Dyadic

section Increment

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {s t : ℝ} (hs : 0 < s) (hst : s < t)

include hw hwm hs hst in
include hℱ in

theorem _root_.Prove2MeSourceProof.h_6839e78f61d86c5ab0f11397 (hG : G.Adapted ℱ)
    (hwa : @StronglyMeasurable Ω ℝ _ (ℱ s) w) :
    ∫ ω, (w ω * (G.integral N t ω - G.integral N s ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ σ in Set.Ioc s t, (G.eval σ e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := (G.incr w hw hwm s t hs hst).integral_full_sq N hℱ (hG.incr hw hwm hs hst hwa)
    (g.incr_horizon_le s t hs hst)
  have hL : ∫ ω, ((G.incr w hw hwm s t hs hst).full N ω) ^ 2 ∂P
      = ∫ ω, (w ω * (G.integral N t ω - G.integral N s ω)) ^ 2 ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [_root_.Prove2MeSourceProof.h_674b57f2d7b8e4e407676e25 N G hw hwm hs hst] with ω hω
    rw [hω]
  rw [← hL, key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  simp_rw [_root_.Prove2MeSourceProof.h_5608c3a7eb7b3d3f0d0b6fe4]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  have hsub : Set.Ioc s t ⊆ Set.Icc 0 t := fun σ hσ => ⟨hs.le.trans hσ.1.le, hσ.2⟩
  rw [← Set.inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun σ _ => ?_
  by_cases hσ : σ ∈ Set.Ioc s t
  · rw [Set.indicator_of_mem hσ, if_pos (Set.mem_Ioc.1 hσ)]
    ring
  · rw [Set.indicator_of_notMem hσ, if_neg (fun h => hσ (Set.mem_Ioc.2 h))]
    ring
end Increment

end MarkStep

end LevyStochCalc.Poisson.Compensated


