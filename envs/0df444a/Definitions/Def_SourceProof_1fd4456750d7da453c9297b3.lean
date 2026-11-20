-- Prove2me | Definitions.Def_SourceProof_1fd4456750d7da453c9297b3
-- name    : SourceProof_1fd4456750d7da453c9297b3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T11:04:31.52961+00:00
-- url     : https://prove2.me/theorems/8edb79bc-1c14-44c0-ae39-aa3394ca7f09
-- title:
--   LevyStochCalc source module: SourceProof_1fd4456750d7da453c9297b3
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.SimplePredictable.eval_eq_sum_indicator` comes from the `LevyStochCalc.Poisson.CompensatedSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Compensated Poisson integral: simple predictable integrands

The simple predictable integrands `φ = ∑_i ξ_i · 1_{(t_i, t_{i+1}] × A_i}` and
their integral `simpleIntegral` against the compensated Poisson measure
`Ñ(dt, de) := N(dt, de) − ν(de) dt`, with the indicator/rectangle bookkeeping
lemmas. The moment identities are in `Poisson/CompensatedMoments.lean`; the
L²-isometry in `Poisson/CompensatedIsometry.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]


theorem _root_.Prove2MeSourceProof.h_1fd4456750d7da453c9297b3
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    φ.eval s e ω = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ : ℝ × E => φ.ξ i ω) (s, e) := by
  unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.eval
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i
  · rw [if_pos h]
    have h_mem : (s, e) ∈ φ.fullRect i := by
      unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.fullRect
      exact Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨h.1, h.2.1⟩, h.2.2⟩
    exact (Set.indicator_of_mem h_mem (fun _ : ℝ × E => φ.ξ i ω)).symm
  · rw [if_neg h]
    have h_not_mem : (s, e) ∉ φ.fullRect i := by
      unfold LevyStochCalc.Poisson.Compensated.SimplePredictable.fullRect
      intro hmem
      obtain ⟨ht, he⟩ := Set.mem_prod.mp hmem
      obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp ht
      exact h ⟨h1, h2, he⟩
    exact (Set.indicator_of_notMem h_not_mem (fun _ : ℝ × E => φ.ξ i ω)).symm
end LevyStochCalc.Poisson.Compensated


