-- Prove2me | Definitions.Def_SourceProof_1b3d64819f52c9f5cf5f792e
-- name    : SourceProof_1b3d64819f52c9f5cf5f792e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:31:02.903946+00:00
-- url     : https://prove2.me/theorems/aa338cdc-3d1b-4ee5-9d18-a099622fc53e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsUIMartingale.const_smul

import Definitions.Def_SourceProof_1aa8fa3c0942e35b7eee3422
import Definitions.Def_SourceProof_543644674db164bf73853b19
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping and linear stability of Protter local martingales

Fundamental sequences are actual witnesses. A shared localizer is the pointwise
minimum of two existing localizers. Its time-zero mask is the intersection of
their masks; the unmasked Klenke definition is not silently substituted.

Source: Protter I.48 (stopping and linear operations).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X Y : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

namespace IsUIMartingale
theorem _root_.Prove2MeSourceProof.h_1b3d64819f52c9f5cf5f792e (hX : IsUIMartingale X F P) (c : ℝ) :
    IsUIMartingale (c • X) F P := by
  obtain ⟨Z, hi, hc⟩ := (_root_.Prove2MeSourceProof.h_1aa8fa3c0942e35b7eee3422 hX.1) hX.2
  refine ⟨hX.1.smul c, _root_.Prove2MeSourceProof.h_543644674db164bf73853b19 (F := F)
    (hi.smul c) (fun t ↦ ?_)⟩
  exact ((hc t).const_smul c).trans (condExp_smul (μ := P) c Z (F t)).symm
end IsUIMartingale

end ProbabilityTheory


