-- Prove2me | Definitions.Def_SourceProof_6112cafec42c0a69bf932916
-- name    : SourceProof_6112cafec42c0a69bf932916
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T12:30:25.194499+00:00
-- url     : https://prove2.me/theorems/14cacdbc-a8cc-402f-8326-5db0ce811415
-- title:
--   LevyStochCalc source module: SourceProof_6112cafec42c0a69bf932916
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.Compensated.SimplePredictable.eval_sq_eq_sum_indicator` comes from the `LevyStochCalc.Poisson.CompensatedSimple` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedSimple_F001
import Definitions.Def_SourceProof_1fd4456750d7da453c9297b3

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


theorem _root_.Prove2MeSourceProof.h_6112cafec42c0a69bf932916
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) :
    (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin φ.N,
      (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) := by
  rw [_root_.Prove2MeSourceProof.h_1fd4456750d7da453c9297b3]
  by_cases h_any : ∃ i : Fin φ.N, (s, e) ∈ φ.fullRect i
  · obtain ⟨i₀, hi₀⟩ := h_any
    have h_unique : ∀ j : Fin φ.N, j ≠ i₀ → (s, e) ∉ φ.fullRect j := by
      intro j hj hj_mem
      have := φ.fullRect_disjoint hj
      exact Set.disjoint_left.mp this hj_mem hi₀
    have h_sum_eq : (∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => φ.ξ i ω) (s, e)) = φ.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    have h_sum_sq_eq : (∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e))
        = (‖φ.ξ i₀ ω‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq, h_sum_sq_eq]
  · push Not at h_any
    have h_zero : ∀ i : Fin φ.N, (φ.fullRect i).indicator (fun _ => φ.ξ i ω) (s, e) = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    have h_zero_sq : ∀ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    rw [Finset.sum_eq_zero (fun i _ => h_zero i),
        Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
    simp
end LevyStochCalc.Poisson.Compensated


