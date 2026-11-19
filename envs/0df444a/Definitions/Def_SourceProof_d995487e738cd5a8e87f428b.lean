-- Prove2me | Definitions.Def_SourceProof_d995487e738cd5a8e87f428b
-- name    : SourceProof_d995487e738cd5a8e87f428b
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T22:02:48.788647+00:00
-- url     : https://prove2.me/theorems/cc0096c7-254c-4592-8b84-957a0c2af2a0
-- title:
--   LevyStochCalc source proof: LevyStochCalc.Probability.norm_le_of_le_exitTime
-- statement:
--   Auxiliary theorem proved in the original LevyStochCalc source. Its proof and dependencies are retained verbatim from the certified extraction.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_ExitTime_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exit times of a process with continuous paths

`exitTime X k ω` is the first nonnegative time at which the path `X ω` has norm at least `k`, and
`⊤` when the path never reaches that norm. For continuous paths the comparison `exitTime X k ω ≤ t`
is decided by the values of the path on the rationals of `[0, t]`, so the exit time is a stopping
time for any filtration the process is adapted to. Letting `k` grow gives a localising sequence:
every time lies strictly below `exitTime X k` for all large `k`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [NormedAddCommGroup E]


theorem _root_.Prove2MeSourceProof.h_d995487e738cd5a8e87f428b {X : Ω → ℝ → E} {ω : Ω} (hX : Continuous (X ω)) {k s : ℝ}
    (hs : 0 < s) (hle : (s : WithTop ℝ) ≤ exitTime X k ω) : ‖X ω s‖ ≤ k := by
  classical
  have hnot : ∀ u : ℝ, 0 ≤ u → u < s → ‖X ω u‖ ≤ k := by
    intro u hu0 hus
    by_contra hcon
    have hmem : u ∈ LevyStochCalc.Probability.exitSet X k ω := ⟨hu0, (not_le.mp hcon).le⟩
    have : LevyStochCalc.Probability.exitTime X k ω ≤ ((u : ℝ) : WithTop ℝ) := by
      rw [LevyStochCalc.Probability.exitTime, if_pos ⟨u, hmem⟩]
      exact_mod_cast csInf_le (LevyStochCalc.Probability.bddBelow_exitSet X k ω) hmem
    have hsu : ((s : ℝ) : WithTop ℝ) ≤ ((u : ℝ) : WithTop ℝ) := hle.trans this
    exact absurd (by exact_mod_cast hsu : s ≤ u) (not_le.mpr hus)
  have hlim : Filter.Tendsto (fun u => ‖X ω u‖) (nhdsWithin s (Set.Iio s)) (nhds ‖X ω s‖) :=
    (hX.norm.tendsto s).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ u in nhdsWithin s (Set.Iio s), ‖X ω u‖ ≤ k := by
    have h0 : ∀ᶠ u in nhdsWithin s (Set.Iio s), 0 < u :=
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds hs)
    filter_upwards [h0, self_mem_nhdsWithin] with u hu0 huc
    exact hnot u hu0.le huc
  exact le_of_tendsto hlim hev
end LevyStochCalc.Probability


