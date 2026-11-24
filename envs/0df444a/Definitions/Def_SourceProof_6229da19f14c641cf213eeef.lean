-- Prove2me | Definitions.Def_SourceProof_6229da19f14c641cf213eeef
-- name    : SourceProof_6229da19f14c641cf213eeef
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:13:35.185684+00:00
-- url     : https://prove2.me/theorems/0424d703-e4c3-4d52-b062-10c68f426f29
-- title:
--   StochLean source theorem: ProbabilityTheory.Indistinguishable.stoppedValueWithTerminal

import Definitions.Def_StochLean_Probability_Process_Equivalence_F000
import Definitions.Def_SourceProof_407218b22ae1495f01bcf52b
import Definitions.Def_SourceProof_6da37c641e8d3b5ccb3dfebc

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopped values with an explicitly supplied value at infinity

Mathlib's finite-time stopped value is retained whenever the stopping time is
finite. At infinity the supplied terminal variable is used instead of the
totalized `untopA` evaluation. Truncated stopped values converge to this owner
when the process has the stated full-half-line terminal limit.
-/

@[expose] public section

open Filter ProbabilityTheory
open scoped NNReal Topology

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℝ≥0 → Ω → E} {Z : Ω → E} {τ : Ω → WithTop ℝ≥0}

end MeasureTheory

namespace ProbabilityTheory.Indistinguishable

open MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X Y : ℝ≥0 → Ω → E} {Z W : Ω → E}

theorem _root_.Prove2MeSourceProof.h_6229da19f14c641cf213eeef (hXY : Indistinguishable X Y P) (hZW : Z =ᵐ[P] W)
    (τ : Ω → WithTop ℝ≥0) :
    MeasureTheory.stoppedValueWithTerminal X Z τ =ᵐ[P]
      MeasureTheory.stoppedValueWithTerminal Y W τ := by
  filter_upwards [hXY, hZW] with ω hXYω hZWω
  by_cases hτ : τ ω = ⊤
  · simp only [_root_.Prove2MeSourceProof.h_407218b22ae1495f01bcf52b hτ, hZWω]
  · simp only [_root_.Prove2MeSourceProof.h_6da37c641e8d3b5ccb3dfebc hτ]
    exact hXYω (τ ω).untopA
end ProbabilityTheory.Indistinguishable


