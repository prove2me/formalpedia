-- Prove2me | Definitions.Def_SourceProof_e46e0dc5c645a65952f0c22f
-- name    : SourceProof_e46e0dc5c645a65952f0c22f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:31.348093+00:00
-- url     : https://prove2.me/theorems/1d4a812a-2009-47a5-a79f-e9baa62095d8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLevyMeasure.iUnion_spanningLevel

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyMeasure_F003
import Definitions.Def_SourceProof_30133bca5f6836331accc046
import Definitions.Def_SourceProof_6132ae08b0208d84e9cba7c3

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

theorem _root_.Prove2MeSourceProof.h_e46e0dc5c645a65952f0c22f : (⋃ n, spanningLevel n) = ({0} : Set ℝ)ᶜ := by
  ext x
  constructor
  · intro hxU hx
    rw [Set.mem_iUnion] at hxU
    obtain ⟨n, hn⟩ := hxU
    subst x
    simpa [ProbabilityTheory.IsLevyMeasure.spanningLevel] using hn
  · intro hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hpos : 0 < ProbabilityTheory.levyIntegrand x := _root_.Prove2MeSourceProof.h_30133bca5f6836331accc046 hx0
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hpos.ne'
    have hn0 : n ≠ 0 := by
      intro hn0
      subst n
      simp at hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact Set.mem_iUnion.mpr ⟨m, hn.le⟩
end IsLevyMeasure

end ProbabilityTheory


