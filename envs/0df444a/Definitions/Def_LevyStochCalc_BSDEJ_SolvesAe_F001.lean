-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_SolvesAe_F001
-- name    : LevyStochCalc_BSDEJ_SolvesAe_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:55:08.607009+00:00
-- url     : https://prove2.me/theorems/23e48830-b7aa-4b4e-a517-c0efb89f4641
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.SolvesAe
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.SolvesAe. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_SolvesAe_F000
import Definitions.Def_SourceProof_7b4e5977b4bcff46a7cd24ec

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Solutions of a BSDEJ up to a null set of sample points

`SolvesBSDEJAe D f ξ T Y Z U` is the solution predicate `SolvesBSDEJ D f ξ T Y Z U` with its
three everywhere-quantified path conditions — right-continuity with left limits of `Y`, and the
vanishing of `Z` and of `U` off the horizon — asked only for almost every sample point.

The two predicates describe the same solutions: setting the three processes to `0` on a
measurable null superset of the exceptional set produces a `SolvesBSDEJ` triple whose paths agree
with the given ones off that null set (`SolvesBSDEJAe.exists_modification`), so the value
processes of two almost-everywhere solutions of the same equation remain indistinguishable on the
horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- A solution holding off a null set of sample points has a modification that is a solution in
the everywhere-quantified sense, with the same value, control and jump processes at each time up
to a null set of sample points. -/
theorem SolvesBSDEJAe.exists_modification
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJAe D f ξ T Y Z U) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' ∧ (∀ t : ℝ, Y' t =ᵐ[P] Y t) ∧ (∀ t : ℝ, Z' t =ᵐ[P] Z t)
        ∧ ∀ t : ℝ, ∀ᵐ ω ∂P, U' t ω = U t ω := by
  obtain ⟨Y', Z', U', hsol, hY, hZ, hU⟩ := (_root_.Prove2MeSourceProof.h_7b4e5977b4bcff46a7cd24ec h)
  refine ⟨Y', Z', U', hsol, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · filter_upwards [hY] with ω hω using hω t
  · filter_upwards [hZ] with ω hω using hω t
  · filter_upwards [hU] with ω hω using hω t
/-- The value processes of two solutions of the same backward equation holding off a null set of
sample points are indistinguishable on the horizon: on a single set of full measure they agree at
every time of `[0, T]`. -/
theorem SolvesBSDEJAe.unique_Y_indistinguishable
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJAe D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJAe D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t ω = Y₂ t ω := by
  obtain ⟨Y₁', Z₁', U₁', hs₁, hm₁, -, -⟩ := (_root_.Prove2MeSourceProof.h_7b4e5977b4bcff46a7cd24ec h₁)
  obtain ⟨Y₂', Z₂', U₂', hs₂, hm₂, -, -⟩ := (_root_.Prove2MeSourceProof.h_7b4e5977b4bcff46a7cd24ec h₂)
  filter_upwards [(_root_.Prove2MeSourceProof.h_437d474ddf6936b4bad36222 hs₁) hs₂ hT hf hL hlip hf0, hm₁, hm₂]
    with ω hω b1 b2
  intro t ht
  rw [← b1 t, ← b2 t]
  exact hω t ht
end LevyStochCalc.BSDEJ.Solves


