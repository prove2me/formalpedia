-- Prove2me | Definitions.Def_SourceProof_e0ac148a71832ad384c26210
-- name    : SourceProof_e0ac148a71832ad384c26210
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T16:59:22.694901+00:00
-- url     : https://prove2.me/theorems/33a7f9eb-80c9-42a3-a52f-54e817aae5b0
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# A.e. measurability for the infimum of a decreasing sequence of σ-algebras

A real function a.e.-measurable for every member of an antitone sequence of sub-σ-algebras is
a.e.-measurable for their infimum. The witness is the `limsup` of the approximants: dropping the
first `N` terms does not change a `limsup`, and after that every approximant is `m N`-measurable,
while on the a.e. set where all the approximants agree with `f` the `limsup` is `f` itself.

This is the step that identifies `⨅ n, lpMeas (m n)` with `lpMeas (⨅ n, m n)`, which is what turns
the convergence of orthogonal projections (`LevyStochCalc/Probability/ProjectionLimit.lean`) into
convergence of conditional expectations along a decreasing filtration.
-/

open MeasureTheory Filter
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}


theorem _root_.Prove2MeSourceProof.h_e0ac148a71832ad384c26210 {m : ℕ → MeasurableSpace Ω} (hanti : Antitone m)
    {f : Ω → ℝ} (hf : ∀ n, AEStronglyMeasurable[m n] f μ) :
    AEStronglyMeasurable[⨅ n, m n] f μ := by
  choose g hg hfg using hf
  refine ⟨fun ω => limsup (fun n => g n ω) atTop, ?_, ?_⟩
  · rw [stronglyMeasurable_iff_measurable]
    intro s hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro N
    have key : (fun ω => limsup (fun n => g n ω) atTop)
        = fun ω => limsup (fun n => g (n + N) ω) atTop := by
      funext ω
      exact (limsup_nat_add (fun n => g n ω) N).symm
    have hmeasN : Measurable[m N] fun ω => limsup (fun n => g n ω) atTop := by
      rw [key]
      refine Measurable.limsup fun n => ?_
      exact (hg (n + N)).measurable.mono (hanti (Nat.le_add_left N n)) le_rfl
    exact hmeasN hs
  · filter_upwards [ae_all_iff.2 hfg] with ω hω
    have : (fun n => g n ω) = fun _ => f ω := funext fun n => (hω n).symm
    rw [this]
    simp
end LevyStochCalc.Probability


