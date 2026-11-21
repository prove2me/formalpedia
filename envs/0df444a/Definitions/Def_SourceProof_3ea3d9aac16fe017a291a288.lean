-- Prove2me | Definitions.Def_SourceProof_3ea3d9aac16fe017a291a288
-- name    : SourceProof_3ea3d9aac16fe017a291a288
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:44:01.057169+00:00
-- url     : https://prove2.me/theorems/3f8b5b00-ab96-4c73-961a-478d77cef5ff
-- title:
--   LevyStochCalc source module: SourceProof_3ea3d9aac16fe017a291a288
-- statement:
--   The original source theorem `LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont` comes from the `LevyStochCalc.Ito.PicardGlobal` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardWindow_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# From window solutions to a solution on `[0, ∞)`

The Bielecki contraction produces a solution on each finite window. Uniqueness on the shorter of
two windows makes the family consistent, and right-continuity upgrades that to an almost-sure
agreement of whole paths, so the windows can be glued along `⌈t⌉₊` into a single path map that
restricts to a window solution on every `[0, T]`.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### Right-continuity upgrades per-time equality to path equality -/

omit [MeasurableSpace E] [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_3ea3d9aac16fe017a291a288 {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) T → A (q : ℝ) ω = B (q : ℝ) ω := by
    rw [MeasureTheory.ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Set.Icc (0 : ℝ) T
    · filter_upwards [h (q : ℝ) hq] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hq' => absurd hq' hq
  have hend : ∀ᵐ ω ∂P, (0 : ℝ) ≤ T → A T ω = B T ω := by
    by_cases hT : (0 : ℝ) ≤ T
    · filter_upwards [h T ⟨hT, le_rfl⟩] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun _ hT' => absurd hT' hT
  filter_upwards [hA, hB, hrat, hend] with ω hAω hBω hqω hTω
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq]
    exact hTω (ht.1.trans ht.2)
  · have hex : ∀ k : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((k : ℝ) + 1)) T := by
      intro k
      refine exists_rat_btwn (lt_min ?_ hlt)
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    choose q hq1 hq2 using hex
    have hqIcc : ∀ k, ((q k : ℝ)) ∈ Set.Icc (0 : ℝ) T := fun k =>
      ⟨(ht.1.trans_lt (hq1 k)).le, ((hq2 k).trans_le (min_le_right _ _)).le⟩
    have htend : Filter.Tendsto (fun k : ℕ => (q k : ℝ)) Filter.atTop
        (nhdsWithin t (Set.Ioi t)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Filter.Eventually.of_forall fun k => hq1 k⟩
      have hub : ∀ k : ℕ, (q k : ℝ) ≤ t + 1 / ((k : ℝ) + 1) := fun k =>
        ((hq2 k).trans_le (min_le_left _ _)).le
      have hlb : ∀ k : ℕ, t ≤ (q k : ℝ) := fun k => (hq1 k).le
      have hupper : Filter.Tendsto (fun k : ℕ => t + 1 / ((k : ℝ) + 1)) Filter.atTop (nhds t) := by
        have := tendsto_const_nhds (x := t) (f := Filter.atTop (α := ℕ)) |>.add
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hlb hub
    have h1 := (hAω t).comp htend
    have h2 := (hBω t).comp htend
    have heqq : ((fun s => A s ω) ∘ fun k : ℕ => (q k : ℝ))
        = ((fun s => B s ω) ∘ fun k : ℕ => (q k : ℝ)) :=
      funext fun k => hqω (q k) (hqIcc k)
    rw [heqq] at h1
    exact tendsto_nhds_unique h1 h2
/-! ### The glued path map -/

/-! ### Consistency of a family of window solutions -/

section Glue

variable {ν : Measure E} [SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)

end Glue

end LevyStochCalc.Ito.Picard


