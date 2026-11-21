-- Prove2me | Definitions.Def_SourceProof_d6ed8f97bdea5b0368dd302f
-- name    : SourceProof_d6ed8f97bdea5b0368dd302f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T20:15:46.164315+00:00
-- url     : https://prove2.me/theorems/380c4d52-f8b3-4819-9026-373934383596
-- title:
--   LevyStochCalc source module: SourceProof_d6ed8f97bdea5b0368dd302f
-- statement:
--   The original source theorem `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` comes from the `LevyStochCalc.Probability.MarkedPredictableComp` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_MarkedPredictableComp_F000
import Definitions.Def_SourceProof_ad0e73cfa88ab4d66c003162

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Marked predictability under measurable post-composition

On the positive times the time coordinate of the time–mark space is measurable for the marked
predictable σ-algebra, a predictable process of the time and the sample point lifts to a marked
predictable one, and a marked predictable process keeps its measurability. A measurable function
of the time, a predictable process and a marked predictable process is therefore marked
predictable once it is cut to the positive times.

## Main statements

* `LevyStochCalc.Probability.measurableSet_markedPredictableSigma_time_pos` — a measurable set
  of positive times, carrying all sample points and marks, is marked predictable.
* `LevyStochCalc.Probability.measurable_markedPredictableSigma_time_pos` — the time coordinate,
  cut to the positive times, is marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` — a measurable function of the
  time, a predictable process and a marked predictable process, cut to the positive times, is
  marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_continuous` — the same for a continuous
  function.

## References

* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {E : Type v} [MeasurableSpace E] {ν : Measure E}

section Time

end Time

section Comp


theorem _root_.Prove2MeSourceProof.h_d6ed8f97bdea5b0368dd302f [SigmaFinite ν] {F₁ : Type*} {F₂ : Type*}
    {F₃ : Type*} [MeasurableSpace F₁] [MeasurableSpace F₂] [MeasurableSpace F₃] [Zero F₃]
    {F : ℝ × F₁ × F₂ → F₃} (hF : Measurable F) {Y : Ω → ℝ → F₁}
    (hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1)
    {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 := by
  classical
  have hpos := LevyStochCalc.Probability.measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  have h1 : Measurable[LevyStochCalc.Probability.traceSigma (LevyStochCalc.Probability.markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => p.2.1 := by
    intro S hS
    change MeasurableSet[LevyStochCalc.Probability.markedPredictableSigma ℱ ν] (_ ∩ _)
    have hrw : (fun p : Ω × ℝ × E => p.2.1) ⁻¹' S ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact and_comm
    rw [hrw]
    exact LevyStochCalc.Probability.measurableSet_markedPredictableSigma_time_pos hS
  have h2 : Measurable[LevyStochCalc.Probability.traceSigma (LevyStochCalc.Probability.markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => Y p.1 p.2.1 := fun D hD =>
    _root_.Prove2MeSourceProof.h_ad0e73cfa88ab4d66c003162 (E := E) (ν := ν) (hY hD)
  have h3 : Measurable[LevyStochCalc.Probability.traceSigma (LevyStochCalc.Probability.markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => Γ p.1 p.2.1 p.2.2 := fun D hD => (hΓ hD).inter hpos
  have hcomp : Measurable[LevyStochCalc.Probability.traceSigma (LevyStochCalc.Probability.markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => F (p.2.1, Y p.1 p.2.1, Γ p.1 p.2.1 p.2.2) :=
    hF.comp (h1.prodMk (h2.prodMk h3))
  exact LevyStochCalc.Probability.measurable_markedPredictableSigma_ite_pos fun U hU => hcomp hU
end Comp

end LevyStochCalc.Probability


