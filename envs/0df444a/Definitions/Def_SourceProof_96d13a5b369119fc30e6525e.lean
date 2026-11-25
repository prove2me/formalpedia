-- Prove2me | Definitions.Def_SourceProof_96d13a5b369119fc30e6525e
-- name    : SourceProof_96d13a5b369119fc30e6525e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:31:29.217713+00:00
-- url     : https://prove2.me/theorems/93cc00ec-3a30-53f4-9c6d-92dbfe59d013
-- title:
--   StochLean source theorem: ProbabilityTheory.SimplePredictableRep.integral_combine_add

import Definitions.Def_StochLean_Probability_Process_Semimartingale_SimplePredictable_Algebra_F001
import Definitions.Def_SourceProof_15e5de2b6483fa8bd27008ef
import Definitions.Def_SourceProof_3af6edef675a4b05fcdc4190
import Definitions.Def_SourceProof_45ddff72791f4617f553714f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Algebra of the full source simple predictable class

The operations use actual common stopping-time refinements. Coefficients remain arbitrary
finite random variables, measurable at their left endpoints. Binary Borel operations fixing
`(0, 0)` preserve the class; in particular it is closed under addition and multiplication.
The elementary integral is bilinear, with its source initial term retained.
-/

@[expose] public section

open MeasureTheory Finset
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}

namespace SimplePredictableRep

theorem _root_.Prove2MeSourceProof.h_96d13a5b369119fc30e6525e (H K : SimplePredictableRep F) (X : ℝ≥0 → Ω → ℝ) :
    (H.combine K (· + ·) (measurable_fst.add measurable_snd)).integral X =
      fun ω ↦ H.integral X ω + K.integral X ω := by
  obtain ⟨hH, hK⟩ := ((_root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef H.partition) K.partition).choose_spec
  change (H.combineOn K ((_root_.Prove2MeSourceProof.h_15e5de2b6483fa8bd27008ef H.partition) K.partition).choose
    (fun a b : ℝ ↦ a + b) _).integral X = _
  rw [_root_.Prove2MeSourceProof.h_3af6edef675a4b05fcdc4190, (_root_.Prove2MeSourceProof.h_45ddff72791f4617f553714f H) hH, (_root_.Prove2MeSourceProof.h_45ddff72791f4617f553714f K) hK]
end SimplePredictableRep

namespace IsSimplePredictable

variable {H K : ℝ≥0 → Ω → ℝ}

end IsSimplePredictable
end ProbabilityTheory


