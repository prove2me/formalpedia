-- Prove2me | Definitions.Def_SourceProof_a7deec5abe53c22fffa52848
-- name    : SourceProof_a7deec5abe53c22fffa52848
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:17:22.547542+00:00
-- url     : https://prove2.me/theorems/16802efc-4509-4b46-873a-13b3b214a514
-- title:
--   LevyStochCalc source module: SourceProof_a7deec5abe53c22fffa52848
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_full_clamp` comes from the `LevyStochCalc.Poisson.MarkStepIsometry` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_MarkStepIsometry_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark-step integrands, their compensated integrals and the `L²` isometry

A *mark-step integrand* is a finite sum `∑ᵢ 𝟙_{(pᵢ, pᵢ₊₁]}(s) ∑ₖ ξᵢₖ(ω) 𝟙_{Bₖ}(e)` over a
time grid `0 = p₀ < ⋯ < p_{N₀}` (`TimeGrid`) and finitely many mark sets `Bₖ` of finite
`ν`-measure, with bounded coefficients `ξᵢₖ`. Its compensated integral up to time `t` is
`∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ ∧ t, pᵢ₊₁ ∧ t] × Bₖ)`. Clamping a grid at a time `t` (`TimeGrid.clamp`)
expresses that integral as the integral over the whole clamped horizon, which carries the
`L²` isometry from the horizon to every time, in both real and `ℝ≥0∞` form.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace TimeGrid

variable (g : TimeGrid)

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ) (G : MarkStep Ω E ν g)

end MarkStep

namespace TimeGrid

variable (g : TimeGrid)

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g}

theorem _root_.Prove2MeSourceProof.h_a7deec5abe53c22fffa52848 (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ht : 0 ≤ t) (ω : Ω) : G.integral N t ω = (G.clamp t ht).full N ω := by
  unfold LevyStochCalc.Poisson.Compensated.MarkStep.integral LevyStochCalc.Poisson.Compensated.MarkStep.full
  symm
  refine Finset.sum_subset
    (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t)))
    ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
  refine Finset.sum_eq_zero fun k _ => ?_
  change G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω = 0
  rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
    LevyStochCalc.Poisson.Compensated.MarkStep.compensated_Ioc_self, mul_zero]
section Eval

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (G : MarkStep Ω E ν g)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ)

end Eval

end MarkStep

end LevyStochCalc.Poisson.Compensated


