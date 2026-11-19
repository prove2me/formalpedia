-- Prove2me | Definitions.Def_LevyStochCalc_Basic_F000
-- name    : LevyStochCalc_Basic_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T21:57:58.003105+00:00
-- url     : https://prove2.me/theorems/093c4ddd-30e1-41e8-8302-b146facb9df6
-- title:
--   LevyStochCalc basic declarations and prerequisites
-- statement:
--   Source-preserving foundational declarations from LevyStochCalc.Basic, including their original proof code and elaboration context.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.MonotoneContinuity

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# LevyStochCalc.Basic

Common imports plus small L² helper lemmas shared across the library:
`eLpNorm` reverse-triangle / difference bounds and L²-continuity (Bochner-L²
limit) lemmas in the plain, Brownian, and compensated-Poisson integrand shapes.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

/-- **Reverse triangle for `eLpNorm` in `tsub` form.** Standard consequence of
`MeasureTheory.eLpNorm_add_le`: for `1 ≤ p`,
`eLpNorm f p μ - eLpNorm g p μ ≤ eLpNorm (f - g) p μ` (ENNReal truncated). -/
lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f g : α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm g p μ
      ≤ MeasureTheory.eLpNorm (f - g) p μ := by
  rw [tsub_le_iff_left]
  have h_decomp : f = g + (f - g) := by ext x; simp
  have h_meas_diff : MeasureTheory.AEStronglyMeasurable (f - g) μ := hf.sub hg
  conv_lhs => rw [h_decomp]
  exact MeasureTheory.eLpNorm_add_le hg h_meas_diff hp
end LevyStochCalc


