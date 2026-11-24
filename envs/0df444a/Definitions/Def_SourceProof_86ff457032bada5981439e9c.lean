-- Prove2me | Definitions.Def_SourceProof_86ff457032bada5981439e9c
-- name    : SourceProof_86ff457032bada5981439e9c
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:16:39.727942+00:00
-- url     : https://prove2.me/theorems/f566d64e-100b-4833-99fb-8aa9130ce20d
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.restrict

import Definitions.Def_SourceProof_153d33725319d021bbb878c0
import Definitions.Def_SourceProof_6e49c08e4f02ca77a891cfb5

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy measures on the real line

The primitive predicate contains exactly the zero-atom condition and finiteness of the truncated
second moment.  Sigma-finiteness is derived by a countable level-set exhaustion and is deliberately
not installed as a global instance.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

namespace IsLevyMeasure

variable {ν : Measure ℝ}


theorem _root_.Prove2MeSourceProof.h_86ff457032bada5981439e9c (hν : IsLevyMeasure ν) (s : Set ℝ) : IsLevyMeasure (ν.restrict s) := by
  constructor
  · rw [Measure.restrict_apply (MeasurableSet.singleton 0)]
    apply le_antisymm _ bot_le
    exact (measure_mono Set.inter_subset_left).trans_eq (_root_.Prove2MeSourceProof.h_6e49c08e4f02ca77a891cfb5 hν)
  · exact lt_of_le_of_lt (lintegral_mono' Measure.restrict_le_self le_rfl)
      (_root_.Prove2MeSourceProof.h_153d33725319d021bbb878c0 hν)
end IsLevyMeasure

end ProbabilityTheory


