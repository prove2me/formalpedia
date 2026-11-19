-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F000
-- name    : LevyStochCalc_Analysis_CadlagJumps_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:55:22.776012+00:00
-- url     : https://prove2.me/theorems/22044d16-e537-4acd-a599-752cb62a37ba
-- title:
--   Source declarations: LevyStochCalc.Analysis.CadlagJumps
-- statement:
--   Source-preserving Lean declaration bundle from LevyStochCalc.Analysis.CadlagJumps, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

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

/-- A bound on a function just left of a point bounds its left limit there. -/
theorem abs_leftLim_sub_le {f : ℝ → ℝ} {s a c r : ℝ} (has : a < s)
    (hL : ∃ L : ℝ, Tendsto f (𝓝[<] s) (𝓝 L)) (h : ∀ u ∈ Set.Ioo a s, |f u - c| ≤ r) :
    |Function.leftLim f s - c| ≤ r := by
  obtain ⟨L, hLt⟩ := hL
  have hlim : Function.leftLim f s = L := leftLim_eq_of_tendsto hLt
  rw [hlim]
  have hev : ∀ᶠ u in 𝓝[<] s, |f u - c| ≤ r := by
    filter_upwards [Ioo_mem_nhdsLT has] with u hu
    exact h u hu
  exact le_of_tendsto ((hLt.sub_const c).abs) hev
end LevyStochCalc.Analysis


