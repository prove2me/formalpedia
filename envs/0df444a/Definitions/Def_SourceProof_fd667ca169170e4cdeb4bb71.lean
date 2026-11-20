-- Prove2me | Definitions.Def_SourceProof_fd667ca169170e4cdeb4bb71
-- name    : SourceProof_fd667ca169170e4cdeb4bb71
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T16:26:31.859582+00:00
-- url     : https://prove2.me/theorems/8bff1553-1248-4905-8098-ead0cccc76b1
-- title:
--   LevyStochCalc source module: SourceProof_fd667ca169170e4cdeb4bb71
-- statement:
--   The original source theorem `LevyStochCalc.Poisson.isStoppingTime_jumpTime_of_complete` comes from the `LevyStochCalc.Poisson.JumpTimesComplete` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F001
import Definitions.Def_LevyStochCalc_Poisson_JumpTimes_F002

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Arrival times as stopping times for a filtration containing the null sets

For a filtration whose time-zero σ-algebra contains the `P`-null sets, the arrival times
`jumpTime N A i` of a Poisson random measure `N` in a mark set `A` of finite intensity are
stopping times for the filtration itself: the counting process is almost surely finite at every
time, and the exceptional set is absorbed by the null sets of the time-zero σ-algebra. This
avoids both the pathwise finiteness hypothesis of `isStoppingTime_jumpTime` and the passage to
the right-continuous filtration in `isStoppingTime_jumpTime_rightCont`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : PoissonRandomMeasure P ν) (A : Set E)


theorem _root_.Prove2MeSourceProof.h_fd667ca169170e4cdeb4bb71 {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by
  obtain ⟨B, hsubB, hBm, hB0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (LevyStochCalc.Poisson.ae_forall_arrivalCount_ne_top N A hA hAν))
  have hGfin : ∀ ω : Ω, ω ∉ B → ∀ s : ℝ, LevyStochCalc.Poisson.arrivalCount N A s ω ≠ ⊤ := by
    intro ω hω s hcon
    exact hω (hsubB fun h => h s hcon)
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω : Ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h0 : ((0 : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ) :=
        (LevyStochCalc.Poisson.coe_zero_le_jumpTime N A i ω).trans hle
      exact absurd (by exact_mod_cast h0 : (0 : ℝ) ≤ t) (not_le.mpr ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have ht' : (0 : ℝ) ≤ t := ht
    have hSamb : MeasurableSet {ω : Ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)} :=
      ℱ.rightCont.le t _ (LevyStochCalc.Poisson.isStoppingTime_jumpTime_rightCont N A hℱ hA i t)
    have hSB : MeasurableSet[ℱ t] ({ω : Ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)} ∩ B) :=
      ℱ.mono ht' _
        (hnull _ (hSamb.inter hBm) (measure_mono_null Set.inter_subset_right hB0))
    have hBc : MeasurableSet[ℱ t] (Bᶜ : Set Ω) := ℱ.mono ht' _ (hnull B hBm hB0).compl
    have hcount : MeasurableSet[ℱ t] {ω : Ω | (i : ℝ≥0∞) ≤ LevyStochCalc.Poisson.arrivalCount N A t ω} :=
      LevyStochCalc.Poisson.measurable_arrivalCount N A hℱ hA t measurableSet_Ici
    have hsplit : {ω : Ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)}
        = ({ω : Ω | (i : ℝ≥0∞) ≤ LevyStochCalc.Poisson.arrivalCount N A t ω} ∩ Bᶜ)
          ∪ ({ω : Ω | LevyStochCalc.Poisson.jumpTime N A i ω ≤ (t : WithTop ℝ)} ∩ B) := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · intro hS
        by_cases hω : ω ∈ B
        · exact Or.inr ⟨hS, hω⟩
        · exact Or.inl ⟨(_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA ht' (hGfin ω hω (t + 1))).mp hS, hω⟩
      · rintro (⟨hc, hω⟩ | ⟨hS, -⟩)
        · exact (_root_.Prove2MeSourceProof.h_89951611d96c791ecb431bce N A hA ht' (hGfin ω hω (t + 1))).mpr hc
        · exact hS
    rw [hsplit]
    exact (hcount.inter hBc).union hSB
end LevyStochCalc.Poisson


