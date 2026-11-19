-- Prove2me | Definitions.Def_SourceProof_0efef36d22ac9421e0560dc4
-- name    : SourceProof_0efef36d22ac9421e0560dc4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:31:07.343316+00:00
-- url     : https://prove2.me/theorems/5bbbeb70-7bf4-4cf7-a427-767cc853fe2c
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.measurableSet_stoppedRegion
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_StoppedProgressive_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a progressively measurable process

Cutting a process off at a stopping time keeps it progressively measurable: before a time `t` the
region `{(ω, s) : s ≤ t, s ≤ τ ω}` is the complement, inside `Ω × (-∞, t]`, of a countable union
of rectangles `{τ ≤ q} × (q, t]` over the rationals, each measurable for the σ-algebra at `t`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}


theorem _root_.Prove2MeSourceProof.h_0efef36d22ac9421e0560dc4 {ℱ : Filtration ℝ mΩ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (t : ℝ) :
    MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] (stoppedRegion τ t) := by
  letI : MeasurableSpace Ω := ℱ t
  set U : Set (Ω × ℝ) := ⋃ q : ℚ, {ω : Ω | τ ω ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)}
    ×ˢ (Set.Ioi (q : ℝ) ∩ Set.Iic t) with hUdef
  have hU : MeasurableSet[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance] U := by
    refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
    · exact (ℱ.mono (min_le_right (q : ℝ) t)) _ (hτ (min (q : ℝ) t))
    · exact measurableSet_Ioi.inter measurableSet_Iic
  have heq : LevyStochCalc.Probability.stoppedRegion τ t = (Set.univ ×ˢ Set.Iic t) \ U := by
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨Set.mem_univ _, h1⟩, ?_⟩
      rw [hUdef]
      rintro hmem
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨hq1, hq2⟩ := hq
      have hle : ((p.2 : ℝ) : WithTop ℝ) ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ) := h2.trans hq1
      have hle' : p.2 ≤ min (q : ℝ) t := by exact_mod_cast hle
      exact absurd (hle'.trans (min_le_left _ _)) (not_le.mpr hq2.1)
    · rintro ⟨⟨-, h1⟩, h2⟩
      refine ⟨h1, ?_⟩
      by_contra hcon
      rw [not_le] at hcon
      have hne : τ p.1 ≠ ⊤ := by
        intro h
        rw [h] at hcon
        exact absurd hcon (by simp)
      obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
      rw [← hr] at hcon
      have hrlt : r < p.2 := by exact_mod_cast hcon
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
      refine h2 ?_
      rw [hUdef]
      refine Set.mem_iUnion.mpr ⟨q, ?_, ⟨hq2, h1⟩⟩
      change τ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)
      rw [← hr]
      have : r ≤ min (q : ℝ) t := le_min hq1.le (hq1.le.trans (hq2.le.trans h1))
      exact_mod_cast this
  rw [heq]
  exact (MeasurableSet.univ.prod measurableSet_Iic).diff hU
end LevyStochCalc.Probability


