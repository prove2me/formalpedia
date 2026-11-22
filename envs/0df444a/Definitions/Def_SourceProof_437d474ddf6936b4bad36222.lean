-- Prove2me | Definitions.Def_SourceProof_437d474ddf6936b4bad36222
-- name    : SourceProof_437d474ddf6936b4bad36222
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:22:11.006723+00:00
-- url     : https://prove2.me/theorems/f293fa30-8a5c-4ff3-a712-5360d037119f
-- title:
--   LevyStochCalc source module: SourceProof_437d474ddf6936b4bad36222
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_indistinguishable` comes from the `LevyStochCalc.BSDEJ.UniquenessIndistinguishable` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_cb6b32244479a6384f44c988

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Indistinguishability of the value process of a backward equation with jumps

`SolvesBSDEJ.unique_Y_Icc` produces, for each time of the horizon separately, a set of full
measure on which the value processes of two solutions agree, so the exceptional set depends on
the time. Every path of a solution is right-continuous, so one set of full measure serves all
times at once: the clamped rationals `max 0 (min T q)`, `q : ℚ`, form a countable subfamily of
the horizon whose exceptional sets have null union, they approach every `t < T` from the right,
and `T` itself is one of them.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_indistinguishable` — the value processes of
  two solutions agree at every time of the horizon on a single set of full measure.
* `LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ_indistinguishable` — existence together
  with uniqueness whose value-process clause is indistinguishability on the horizon.

## Source

* Delong, "BSDEs with Jumps and their Actuarial and Financial Applications", Springer 2013,
  Theorem 3.1.1.
* Tang & Li, "Necessary conditions for optimal control of stochastic systems with random jumps",
  SICON 32(5), 1994, Theorem 3.1.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}


theorem _root_.Prove2MeSourceProof.h_437d474ddf6936b4bad36222
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJ D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJ D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t ω = Y₂ t ω := by
  have hIcc := _root_.Prove2MeSourceProof.h_cb6b32244479a6384f44c988 h₁ h₂ hT hf hL hlip hf0
  have hmem : ∀ q : ℚ, max (0 : ℝ) (min T (q : ℝ)) ∈ Set.Icc (0 : ℝ) T :=
    fun _ => ⟨le_max_left _ _, max_le hT.le (min_le_left _ _)⟩
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ,
      Y₁ (max (0 : ℝ) (min T (q : ℝ))) ω = Y₂ (max (0 : ℝ) (min T (q : ℝ))) ω :=
    ae_all_iff.mpr fun q => hIcc _ (hmem q)
  filter_upwards [hrat, hIcc T ⟨hT.le, le_rfl⟩] with ω hω hωT
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | htT
  · rw [heq]
    exact hωT
  have hex : ∀ n : ℕ, ∃ q : ℚ, t < (q : ℝ) ∧ (q : ℝ) < min (t + 1 / ((n : ℝ) + 1)) T := by
    intro n
    refine exists_rat_btwn (lt_min ?_ htT)
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  choose q hq1 hq2 using hex
  have hq0 : ∀ n, (0 : ℝ) ≤ (q n : ℝ) := fun n => le_of_lt (lt_of_le_of_lt ht.1 (hq1 n))
  have hqT : ∀ n, (q n : ℝ) ≤ T := fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_right _ _))
  have hclamp : ∀ n, max (0 : ℝ) (min T (q n : ℝ)) = (q n : ℝ) := fun n => by
    rw [min_eq_right (hqT n), max_eq_right (hq0 n)]
  have htend : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝 t) := by
    have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using hc.add hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hq1 n).le)
      (fun n => le_of_lt (lt_of_lt_of_le (hq2 n) (min_le_left _ _)))
  have hsw : Tendsto (fun n : ℕ => (q n : ℝ)) atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend
      (Eventually.of_forall fun n => hq1 n)
  have hl₁ : Tendsto (fun n => Y₁ (q n : ℝ) ω) atTop (𝓝 (Y₁ t ω)) := (h₁.Y_cadlag ω t).1.comp hsw
  have hl₂ : Tendsto (fun n => Y₂ (q n : ℝ) ω) atTop (𝓝 (Y₂ t ω)) := (h₂.Y_cadlag ω t).1.comp hsw
  refine tendsto_nhds_unique (hl₁.congr fun n => ?_) hl₂
  have hn := hω (q n)
  rwa [hclamp n] at hn
end LevyStochCalc.BSDEJ.Solves


