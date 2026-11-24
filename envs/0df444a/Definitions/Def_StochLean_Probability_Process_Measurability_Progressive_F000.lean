-- Prove2me | Definitions.Def_StochLean_Probability_Process_Measurability_Progressive_F000
-- name    : StochLean_Probability_Process_Measurability_Progressive_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T22:07:14.608646+00:00
-- url     : https://prove2.me/theorems/c8663bef-7d88-401c-a196-6f68a3f043ff
-- title:
--   StochLean: Probability.Process.Measurability.Progressive F000

import Definitions.Def_StochLean_Probability_Process_Filtration_Usual_F001
import Definitions.Def_StochLean_Probability_Process_Measurability_Joint_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.Floor

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Progressive measurability from right-continuous paths

For nonnegative real time, a strongly adapted process with right-continuous trajectories is
strongly progressive. The proof uses measurable countable-range right-grid approximations; it
does not strengthen right continuity to continuity.
-/

@[expose] public section

open NNReal TopologicalSpace
open scoped Topology

/-- The upper mesh approximation with spacing `1 / (n + 1)`.  It is kept public because the
same countable-range approximation is also used for finite stopping times. -/
noncomputable def rightGrid (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  (Nat.ceil (((n + 1 : ℕ) : ℝ≥0) * t) : ℝ≥0) / (n + 1 : ℕ)
namespace MeasureTheory

namespace StronglyAdapted

end StronglyAdapted

end MeasureTheory


