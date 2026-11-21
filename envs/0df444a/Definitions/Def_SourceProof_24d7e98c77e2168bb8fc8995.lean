-- Prove2me | Definitions.Def_SourceProof_24d7e98c77e2168bb8fc8995
-- name    : SourceProof_24d7e98c77e2168bb8fc8995
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T10:15:27.81408+00:00
-- url     : https://prove2.me/theorems/28b3b3c6-181a-4aa4-b176-fa93b8462e7b
-- title:
--   LevyStochCalc source module: SourceProof_24d7e98c77e2168bb8fc8995
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.MarkStep.eval_clamp` comes from the `LevyStochCalc.Poisson.MarkStepIsometry` module. The staged Lean declaration includes its source proof and dependency references.
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

theorem _root_.Prove2MeSourceProof.h_24d7e98c77e2168bb8fc8995 (G : MarkStep Ω E ν g) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) (e : E) (ω : Ω) :
    (G.clamp t ht).eval s e ω = if s ≤ t then G.eval s e ω else 0 := by
  unfold LevyStochCalc.Poisson.Compensated.MarkStep.eval
  split_ifs with hst
  · symm
    calc ∑ i ∈ Finset.range g.N₀,
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          symm
          refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
            Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t))) ?_
          intro i hi hni
          rw [Finset.mem_range] at hi hni
          have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
          rw [Set.indicator_of_notMem, zero_mul]
          intro hs
          exact absurd (hst.trans hti) (not_le.2 hs.1)
      _ = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hpi := (g.lt_of_lt_clampIndex hi).2
          congr 1
          rw [min_eq_left hpi.le]
          by_cases hs : s ∈ Set.Ioc (g.p i) (g.p (i + 1))
          · rw [Set.indicator_of_mem hs, Set.indicator_of_mem
              (show s ∈ Set.Ioc (g.p i) (min (g.p (i + 1)) t) from ⟨hs.1, le_min hs.2 hst⟩)]
          · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem]
            intro hs'
            exact hs ⟨hs'.1, hs'.2.trans (min_le_left _ _)⟩
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Set.indicator_of_notMem, zero_mul]
    intro hs
    exact hst (hs.2.trans (min_le_right _ _))
section Eval

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (G : MarkStep Ω E ν g)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ :
  IsPoissonFiltration N ℱ)

end Eval

end MarkStep

end LevyStochCalc.Poisson.Compensated


