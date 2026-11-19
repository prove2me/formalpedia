-- Prove2me | Definitions.Def_SourceProof_1720d71b3049591278c59d6d
-- name    : SourceProof_1720d71b3049591278c59d6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:26:47.502921+00:00
-- url     : https://prove2.me/theorems/784ca3aa-dade-4c7c-9d1f-ae5c58a528f8
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.exists_everywhere_cadlag_modification
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Right-continuous adapted processes are progressively measurable

An adapted process with right-continuous paths is progressively measurable: on `(-∞, i] × Ω` it
is the pointwise limit of the dyadic right-staircases `t ↦ X_{⌈2ⁿt⌉/2ⁿ ∧ i}`, each of which
takes countably many values, all at times bounded by `i`.

## Main statements

* `Probability.dyadicCeil` — the dyadic right-staircase, capped at a horizon.
* `LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous` — a right-continuous
  adapted process is progressively measurable.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_uncurry` — a progressively
  measurable process is jointly measurable.
* `LevyStochCalc.Probability.exists_everywhere_cadlag_modification` — under the usual
  conditions, an almost-surely càdlàg adapted process has an everywhere-càdlàg modification.
* `LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc` — the integral
  of a progressively measurable process over `[0, t]` is measurable for `ℱ t`.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


theorem _root_.Prove2MeSourceProof.h_1720d71b3049591278c59d6d
    {P : MeasureTheory.Measure Ω} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {X : ℝ → Ω → ℝ}
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (X t))
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L)) :
    ∃ Y : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Y t)) ∧ (∀ t : ℝ, Y t =ᵐ[P] X t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => Y s ω) (𝓝[<] t) (𝓝 L) := by
  classical
  obtain ⟨N, hsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hcad)
  have hNout : ∀ ω : Ω, ω ∉ N → ∀ t : ℝ,
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω)) ∧
        ∃ L : ℝ, Tendsto (fun s => X s ω) (𝓝[<] t) (𝓝 L) :=
    fun ω hω => not_not.mp fun h => hω (hsub h)
  have hNF : ∀ t : ℝ, MeasurableSet[ℱ t] N := by
    intro t
    rcases le_or_gt 0 t with h | h
    · exact ℱ.mono h _ (hnull N hNmeas hNzero)
    · exact hℱ0 t h.le _ (hnull N hNmeas hNzero)
  refine ⟨fun t ω => if ω ∈ N then 0 else X t ω, fun t => ?_, fun t => ?_, ?_, ?_⟩
  · exact Measurable.piecewise (hNF t) measurable_const (hadapt t)
  · filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω
    simp [Set.notMem_of_mem_compl hω]
  · intro ω t
    by_cases hω : ω ∈ N
    · simp only [hω, if_pos]
      exact tendsto_const_nhds
    · simpa [hω] using (hNout ω hω t).1
  · intro ω t
    by_cases hω : ω ∈ N
    · refine ⟨0, ?_⟩
      simp only [hω, if_pos]
      exact tendsto_const_nhds
    · obtain ⟨L, hL⟩ := (hNout ω hω t).2
      exact ⟨L, by simpa [hω] using hL⟩
end LevyStochCalc.Probability


