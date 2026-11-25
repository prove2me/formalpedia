-- Prove2me | Definitions.Def_SourceProof_ce1f5b736b8d388c0b16537f
-- name    : SourceProof_ce1f5b736b8d388c0b16537f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T14:34:53.082251+00:00
-- url     : https://prove2.me/theorems/7b333e34-1dca-589c-9249-108421a135fb
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.iUnion_levyIdentificationSet

import Definitions.Def_StochLean_Probability_InfinitelyDivisible_LevyKhintchine_F010

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_ce1f5b736b8d388c0b16537f :
    (⋃ n, levyIdentificationSet n) = {0}ᶜ := by
  ext x
  constructor
  · rintro hx
    simp only [Set.mem_iUnion, ProbabilityTheory.LevyTriplet.levyIdentificationSet] at hx
    obtain ⟨n, hx0, -⟩ := hx
    simpa [abs_pos] using hx0
  · intro hx
    have hx0 : x ≠ 0 := by simpa using hx
    obtain ⟨n, hn⟩ := exists_nat_gt (|x| / (2 * Real.pi))
    simp only [Set.mem_iUnion, ProbabilityTheory.LevyTriplet.levyIdentificationSet]
    refine ⟨n, (abs_pos.mpr hx0), ?_⟩
    have hpi : 0 < 2 * Real.pi := by positivity
    have hn' : |x| < 2 * Real.pi * n := by
      simpa [mul_comm] using (div_lt_iff₀ hpi).mp hn
    have hnm : (n : ℝ) ≤ n + 1 := by norm_num
    exact hn'.trans_le (mul_le_mul_of_nonneg_left hnm hpi.le)
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


