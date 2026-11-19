-- Prove2me | Definitions.Def_LevyStochCalc_Probability_MarkedProgressiveSlice_F000
-- name    : LevyStochCalc_Probability_MarkedProgressiveSlice_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:28:02.26486+00:00
-- url     : https://prove2.me/theorems/e47b279c-64a6-4130-8298-48f8ac27d3ed
-- title:
--   Source declarations: LevyStochCalc.Probability.MarkedProgressiveSlice
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Probability.MarkedProgressiveSlice. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_Progressive_F002
import Definitions.Def_SourceProof_e303374519c4de703021a2f6

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Mark slices and right-continuous transfer of progressive measurability

For a marked process `φ : Ω → ℝ → E → F` that is `MarkedProgressivelyMeasurable` for a
filtration `ℱ`, each mark `e : E` gives a slice `(ω, s) ↦ φ ω s e` which is
`ProgressivelyMeasurable` for `ℱ`, and `MarkedProgressivelyMeasurable.mono` transfers marked
progressive measurability along an inclusion of filtrations.

Composing with `ProgressivelyMeasurable.isStronglyProgressive` and the inclusion
`ℱ ≤ ℱ.rightCont` transfers both the scalar and the mark-sliced statements to
`MeasureTheory.IsStronglyProgressive ℱ.rightCont`, in Mathlib's `fun s ω` argument order;
`isStronglyProgressive_rightCont_pi` is the coordinatewise form for processes valued in
`Fin d → ℝ`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Slice

variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]
  {φ : Ω → ℝ → E → F}

/-- The slice of a marked progressively measurable process at a fixed mark is progressively
measurable. -/
theorem MarkedProgressivelyMeasurable.slice (h : MarkedProgressivelyMeasurable ℱ φ) (e : E) :
    ProgressivelyMeasurable ℱ fun ω s => φ ω s e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable fun p : Ω × ℝ => (p.1, p.2, e) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  exact (h t).comp_measurable hg
/-- Marked progressive measurability is monotone in the filtration. -/
theorem MarkedProgressivelyMeasurable.mono {𝒢 : Filtration ℝ mΩ}
    (h : MarkedProgressivelyMeasurable ℱ φ) (hle : ∀ t, ℱ t ≤ 𝒢 t) :
    MarkedProgressivelyMeasurable 𝒢 φ := fun t =>
  (h t).mono (sup_le_sup (MeasurableSpace.comap_mono (hle t)) le_rfl)
end Slice

section Transfer

variable {F : Type*} [TopologicalSpace F] [Zero F] {H : Ω → ℝ → F}

/-- A progressively measurable process is strongly progressive for the right-continuous
filtration `ℱ.rightCont`. -/
theorem ProgressivelyMeasurable.isStronglyProgressive_rightCont
    (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ.rightCont fun s ω => H ω s :=
  (_root_.Prove2MeSourceProof.h_e303374519c4de703021a2f6 (h.mono fun t => ℱ.le_rightCont t))
end Transfer

section Pi

variable {d : ℕ} {Z : ℝ → Ω → Fin d → ℝ}

/-- A process valued in `Fin d → ℝ` whose coordinates are progressively measurable is strongly
progressive for the right-continuous filtration `ℱ.rightCont`. -/
theorem isStronglyProgressive_rightCont_pi
    (h : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z s ω i) :
    IsStronglyProgressive ℱ.rightCont Z := by
  intro t
  letI : MeasurableSpace Ω := ℱ.rightCont t
  refine stronglyMeasurable_iff_measurable.mpr (measurable_pi_lambda _ fun i => ?_)
  exact ((h i).isStronglyProgressive_rightCont t).measurable
end Pi

section MarkedTransfer

variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]
  {U : ℝ → Ω → E → F}

/-- Every mark slice of a marked progressively measurable process is strongly progressive for
the right-continuous filtration `ℱ.rightCont`. -/
theorem MarkedProgressivelyMeasurable.isStronglyProgressive_rightCont
    (h : MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e) :
    ∀ e : E, IsStronglyProgressive ℱ.rightCont fun s ω => U s ω e :=
  fun e => (h.slice e).isStronglyProgressive_rightCont
end MarkedTransfer

end LevyStochCalc.Probability


