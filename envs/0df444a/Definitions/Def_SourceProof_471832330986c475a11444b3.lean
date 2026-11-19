-- Prove2me | Definitions.Def_SourceProof_471832330986c475a11444b3
-- name    : SourceProof_471832330986c475a11444b3
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:00.884986+00:00
-- url     : https://prove2.me/theorems/5b90360e-72b8-4ae2-97a8-063f8713d97b
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Analysis.countable_setOf_ne_leftLim
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_7cf69e2d57fa4024ee430697
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.LeftRightLim

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


theorem _root_.Prove2MeSourceProof.h_471832330986c475a11444b3 {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    {t : ℝ | f t ≠ Function.leftLim f t}.Countable := by
  have hcov : {t : ℝ | f t ≠ Function.leftLim f t}
      = ⋃ n : ℕ, {t : ℝ | 1 / (n + 1 : ℝ) < |f t - Function.leftLim f t|} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      exact exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr h))
    · rintro ⟨n, hn⟩ heq
      rw [heq, sub_self, abs_zero] at hn
      exact absurd hn (not_lt.mpr (by positivity))
  rw [hcov]
  refine Set.countable_iUnion fun n => ?_
  have hε : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  choose δ hδpos hδ using fun t : ℝ => _root_.Prove2MeSourceProof.h_7cf69e2d57fa4024ee430697 hright hleft hε t
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun t : ℝ => Set.Ioo (t - δ t / 2) (t + δ t / 2)) ?_ (fun t _ => isOpen_Ioo)
    (fun t _ => ⟨t, ⟨by linarith [hδpos t], by linarith [hδpos t]⟩⟩)
  intro a ha b hb hab
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have hxa : |x - a| < δ a / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxb : |x - b| < δ b / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hab' : |a - b| < δ a / 2 + δ b / 2 := by
    calc |a - b| ≤ |a - x| + |x - b| := abs_sub_le _ _ _
      _ = |x - a| + |x - b| := by rw [abs_sub_comm a]
      _ < δ a / 2 + δ b / 2 := by linarith
  rw [abs_lt] at hab'
  rcases le_total (δ b) (δ a) with hle | hle
  · have hba : b ∈ Set.Ioo (a - δ a) (a + δ a) := by
      constructor <;> linarith [hab'.1, hab'.2, hδpos b]
    have hjump := hδ a b hba (Ne.symm hab)
    have hb' : 1 / ((n : ℝ) + 1) < |f b - Function.leftLim f b| := hb
    linarith
  · have hab2 : a ∈ Set.Ioo (b - δ b) (b + δ b) := by
      constructor <;> linarith [hab'.1, hab'.2, hδpos a]
    have hjump := hδ b a hab2 hab
    have ha' : 1 / ((n : ℝ) + 1) < |f a - Function.leftLim f a| := ha
    linarith
end LevyStochCalc.Analysis


