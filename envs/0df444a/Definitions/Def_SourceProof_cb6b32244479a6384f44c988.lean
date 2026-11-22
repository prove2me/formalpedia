-- Prove2me | Definitions.Def_SourceProof_cb6b32244479a6384f44c988
-- name    : SourceProof_cb6b32244479a6384f44c988
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:14:29.85585+00:00
-- url     : https://prove2.me/theorems/30d2e9d5-3485-4233-8c3a-6293adefe226
-- title:
--   LevyStochCalc source module: SourceProof_cb6b32244479a6384f44c988
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc` comes from the `LevyStochCalc.BSDEJ.Uniqueness` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Uniqueness_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Uniqueness of solutions of a backward equation with jumps

A solution of a backward equation with jumps over the augmented joint filtration of a Lévy
driver is its own Picard output, so the difference of two solutions with the same generator,
terminal value and horizon is a fixed point of the Picard contraction: its exponentially
weighted norm at the Young weight `max 2 (24 L²)` is at most a quarter of itself and finite,
hence zero. The value processes then agree almost surely at almost every time of the horizon,
and, both being right-continuous, at every time of the horizon; the diffusion coordinates and
the jump integrand agree up to sets of zero energy.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.toPicardOutput` — a solution is its own Picard output.
* `LevyStochCalc.BSDEJ.Solves.exists_drift_of_solvesBSDEJ` — the generator evaluated along a
  solution has a jointly and progressively measurable version of finite energy.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique` — the weighted norm of the difference of two
  solutions vanishes.
* `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_ae`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_Icc`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Z`,
  `LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_U` — the three components of two solutions
  agree.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Auxiliary facts -/

/-! ### A solution is its own Picard output -/

/-! ### The drift along a solution -/

/-! ### Uniqueness -/

/-! ### Consequences -/


theorem _root_.Prove2MeSourceProof.h_cb6b32244479a6384f44c988 {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
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
    ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t =ᵐ[P] Y₂ t := by
  have hae := LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ.unique_Y_ae h₁ h₂ hT hf hL hlip hf0
  have hterm : Y₁ T =ᵐ[P] Y₂ T :=
    ((h₁.toPicardOutput hT).Y_terminal).trans ((h₂.toPicardOutput hT).Y_terminal).symm
  have hB0 : (volume.restrict (Set.Icc (0 : ℝ) T)) {s : ℝ | ¬ Y₁ s =ᵐ[P] Y₂ s} = 0 :=
    ae_iff.mp hae
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | htT
  · rw [heq]
    exact hterm
  have hex : ∀ n : ℕ, ∃ r : ℝ,
      r ∈ Set.Ioc t (t + min (1 / ((n : ℝ) + 1)) (T - t)) ∧ Y₁ r =ᵐ[P] Y₂ r := by
    intro n
    have hpos : 0 < min (1 / ((n : ℝ) + 1)) (T - t) :=
      lt_min (by positivity) (by linarith)
    by_contra hcon
    have hsub : Set.Ioc t (t + min (1 / ((n : ℝ) + 1)) (T - t))
        ⊆ {s : ℝ | ¬ Y₁ s =ᵐ[P] Y₂ s} := fun r hr hgood => hcon ⟨r, hr, hgood⟩
    have hsubI : Set.Ioc t (t + min (1 / ((n : ℝ) + 1)) (T - t)) ⊆ Set.Icc (0 : ℝ) T := by
      intro r hr
      refine ⟨le_of_lt (lt_of_le_of_lt ht.1 hr.1), hr.2.trans ?_⟩
      have := min_le_right (1 / ((n : ℝ) + 1)) (T - t)
      linarith
    have h2 := measure_mono_null hsub hB0
    rw [Measure.restrict_apply measurableSet_Ioc,
      Set.inter_eq_self_of_subset_left hsubI, Real.volume_Ioc,
      add_sub_cancel_left] at h2
    exact absurd (ENNReal.ofReal_eq_zero.mp h2) (not_le.mpr hpos)
  choose r hr1 hr2 using hex
  have hrl : ∀ n, t < r n := fun n => (hr1 n).1
  have hru : ∀ n, r n ≤ t + 1 / ((n : ℝ) + 1) := by
    intro n
    refine (hr1 n).2.trans ?_
    have := min_le_left (1 / ((n : ℝ) + 1)) (T - t)
    linarith
  have htend : Tendsto r atTop (𝓝 t) := by
    have hz : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Tendsto (fun _ : ℕ => t) atTop (𝓝 t) := tendsto_const_nhds
    have hup : Tendsto (fun n : ℕ => t + 1 / ((n : ℝ) + 1)) atTop (𝓝 t) := by
      simpa using hc.add hz
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun n => (hrl n).le) hru
  have hsw : Tendsto r atTop (𝓝[>] t) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r htend
      (Eventually.of_forall fun n => hrl n)
  have hall : ∀ᵐ ω ∂P, ∀ n, Y₁ (r n) ω = Y₂ (r n) ω := ae_all_iff.mpr hr2
  filter_upwards [hall] with ω hω
  have hl₁ : Tendsto (fun n => Y₁ (r n) ω) atTop (𝓝 (Y₁ t ω)) := (h₁.Y_cadlag ω t).1.comp hsw
  have hl₂ : Tendsto (fun n => Y₂ (r n) ω) atTop (𝓝 (Y₂ t ω)) := (h₂.Y_cadlag ω t).1.comp hsw
  exact tendsto_nhds_unique (hl₁.congr fun n => hω n) hl₂
end LevyStochCalc.BSDEJ.Solves


