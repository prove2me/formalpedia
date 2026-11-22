-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_UniquenessIndistinguishable_F000
-- name    : LevyStochCalc_BSDEJ_UniquenessIndistinguishable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:37:58.138429+00:00
-- url     : https://prove2.me/theorems/99bb04eb-4e86-4c35-8c02-af79695d02c2
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.UniquenessIndistinguishable
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.UniquenessIndistinguishable. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_Uniqueness_F000
import Definitions.Def_SourceProof_437d474ddf6936b4bad36222
import Definitions.Def_SourceProof_8d3a16d297de60304d079b21

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

/-- **Existence and uniqueness for a backward equation with jumps, with indistinguishable value
processes.** For a Lipschitz generator square integrable at the origin on the horizon and a square
integrable terminal datum measurable for the augmented joint filtration at the horizon, there is a
solution triple, and any two solution triples have value processes agreeing at every time of the
horizon on a single set of full measure and diffusion and jump integrands whose difference has
vanishing energy on the horizon. -/
theorem exists_unique_solvesBSDEJ_indistinguishable
    (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u : E → ℝ, Measurable fun r : ℝ × ℝ × (Fin d → ℝ) => f r.1 r.2.1 r.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
        SolvesBSDEJ D f ξ T Y Z U) ∧
      ∀ (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)) (U₁ U₂ : ℝ → Ω → E → ℝ),
        SolvesBSDEJ D f ξ T Y₁ Z₁ U₁ → SolvesBSDEJ D f ξ T Y₂ Z₂ U₂ →
          (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t ω = Y₂ t ω) ∧
          (∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) = 0) ∧
          Poisson.Compensated.markedEnergy P ν T (fun ω s e => U₁ s ω e - U₂ s ω e) = 0 :=
  ⟨_root_.Prove2MeSourceProof.h_8d3a16d297de60304d079b21 D f hL hf hlip hT hf0 hξ2 hξm, fun _ _ _ _ _ _ h₁ h₂ =>
    ⟨(_root_.Prove2MeSourceProof.h_437d474ddf6936b4bad36222 h₁) h₂ hT hf hL hlip hf0, h₁.unique_Z h₂ hT hf hL hlip hf0,
      h₁.unique_U h₂ hT hf hL hlip hf0⟩⟩
end LevyStochCalc.BSDEJ.Solves


