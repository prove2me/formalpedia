-- Prove2me | Definitions.Def_SourceProof_7cf69e2d57fa4024ee430697
-- name    : SourceProof_7cf69e2d57fa4024ee430697
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:56:16.268024+00:00
-- url     : https://prove2.me/theorems/6a81a908-7119-42a9-9c25-7a4e5392ed8e
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.exists_isolating_radius
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The jumps of a càdlàg function

A function on the line that is right-continuous and has left limits everywhere jumps only at
isolated points of each level of the jump size, so its jump set is countable and therefore
Lebesgue-null: such a function agrees with its left limits almost everywhere.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace LevyStochCalc.Analysis


theorem _root_.Prove2MeSourceProof.h_7cf69e2d57fa4024ee430697 {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → |f s - Function.leftLim f s| < ε := by
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨δ₁, hδ₁, hr1⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hright t) (ε / 3) hε3
  obtain ⟨L, hLt⟩ := hleft t
  obtain ⟨δ₂, hδ₂, hr2⟩ := Metric.tendsto_nhdsWithin_nhds.mp hLt (ε / 3) hε3
  have h1 : ∀ s, t < s → dist s t < δ₁ → |f s - f t| < ε / 3 := by
    intro s hs hd
    have := hr1 hs hd
    rwa [Real.dist_eq] at this
  have h2 : ∀ s, s < t → dist s t < δ₂ → |f s - L| < ε / 3 := by
    intro s hs hd
    have := hr2 hs hd
    rwa [Real.dist_eq] at this
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hst => ?_⟩
  have hmin₁ : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hmin₂ : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · -- `s` is to the left of `t`
    have hsd : dist s t < δ₂ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : s - t < 0)]
      have := hs.1
      linarith
    have hfs : |f s - L| < ε / 3 := h2 s hlt hsd
    have hls : |Function.leftLim f s - L| ≤ ε / 3 := by
      refine LevyStochCalc.Analysis.abs_leftLim_sub_le (a := t - δ₂) (by linarith [hs.1]) (hleft s) fun u hu => ?_
      have hud : dist u t < δ₂ := by
        rw [Real.dist_eq, abs_of_neg (by linarith [hu.2] : u - t < 0)]
        linarith [hu.1]
      exact (h2 u (by linarith [hu.2]) hud).le
    have htri : |f s - Function.leftLim f s| ≤ |f s - L| + |Function.leftLim f s - L| := by
      calc |f s - Function.leftLim f s| ≤ |f s - L| + |L - Function.leftLim f s| :=
            abs_sub_le _ _ _
        _ = |f s - L| + |Function.leftLim f s - L| := by rw [abs_sub_comm L]
    linarith
  · -- `s` is to the right of `t`
    have hsd : dist s t < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < s - t)]
      have := hs.2
      linarith
    have hfs : |f s - f t| < ε / 3 := h1 s hgt hsd
    have hls : |Function.leftLim f s - f t| ≤ ε / 3 := by
      refine LevyStochCalc.Analysis.abs_leftLim_sub_le (a := t) hgt (hleft s) fun u hu => ?_
      have hud : dist u t < δ₁ := by
        rw [Real.dist_eq, abs_of_pos (by linarith [hu.1] : 0 < u - t)]
        linarith [hu.2, hs.2]
      exact (h1 u hu.1 hud).le
    have htri : |f s - Function.leftLim f s| ≤ |f s - f t| + |Function.leftLim f s - f t| := by
      calc |f s - Function.leftLim f s| ≤ |f s - f t| + |f t - Function.leftLim f s| :=
            abs_sub_le _ _ _
        _ = |f s - f t| + |Function.leftLim f s - f t| := by rw [abs_sub_comm (f t)]
    linarith
end LevyStochCalc.Analysis


