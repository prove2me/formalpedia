-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_StepIntegral_F000
-- name    : StochLean_Analysis_PathVariation_StepIntegral_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:20.246548+00:00
-- url     : https://prove2.me/theorems/f58c4c8d-d00e-4220-83d6-5a1903d3ab9c
-- title:
--   StochLean: Analysis.PathVariation.StepIntegral F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Tactic.Order

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Representation independence of finite interval integration

The integrator is an arbitrary real-valued function. A zero finite linear
combination of half-open interval indicators has zero increment integral.
This is the deterministic algebra behind Protter's elementary integral.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology BigOperators

namespace StochLean

private theorem intervalStep_eventually_right (a b s : ℝ≥0) (c : ℝ) :
    ∀ᶠ t in nhdsWithin s (Ioi s),
      (if a < t ∧ t ≤ b then c else 0) = (if a ≤ s ∧ s < b then c else 0) := by
  by_cases ha : a ≤ s
  · by_cases hb : s < b
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds hb).filter_mono nhdsWithin_le_nhds] with t ht htb
      simp [ha, hb, ha.trans_lt ht, htb.le]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have hbt : b < t := (le_of_not_gt hb).trans_lt ht
      simp [hb, not_le_of_gt hbt]
  · filter_upwards [(eventually_lt_nhds (lt_of_not_ge ha)).filter_mono nhdsWithin_le_nhds]
      with t ht
    simp [ha, not_lt_of_ge ht.le]
end StochLean


