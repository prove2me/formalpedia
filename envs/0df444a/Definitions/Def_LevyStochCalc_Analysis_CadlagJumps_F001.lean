-- Prove2me | Definitions.Def_LevyStochCalc_Analysis_CadlagJumps_F001
-- name    : LevyStochCalc_Analysis_CadlagJumps_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:14:50.189617+00:00
-- url     : https://prove2.me/theorems/2329a9d8-1283-4633-bb98-741e6820248f
-- title:
--   Source declarations: LevyStochCalc.Analysis.CadlagJumps
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Analysis.CadlagJumps. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_SourceProof_471832330986c475a11444b3
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

/-- **A càdlàg function agrees with its left limits almost everywhere.** -/
theorem ae_eq_leftLim_of_cadlag {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ t ∂(volume : Measure ℝ), f t = Function.leftLim f t := by
  rw [ae_iff]
  exact (_root_.Prove2MeSourceProof.h_471832330986c475a11444b3 hright hleft).measure_zero _
end LevyStochCalc.Analysis


