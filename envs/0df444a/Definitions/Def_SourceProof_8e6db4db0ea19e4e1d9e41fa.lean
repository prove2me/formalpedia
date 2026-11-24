-- Prove2me | Definitions.Def_SourceProof_8e6db4db0ea19e4e1d9e41fa
-- name    : SourceProof_8e6db4db0ea19e4e1d9e41fa
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:09.312124+00:00
-- url     : https://prove2.me/theorems/f6575bc5-99e0-430c-bb50-b50d19bafb6f
-- title:
--   StochLean source theorem: ProbabilityTheory.IsCadlagPath.tendsto_atTop_of_separated_samples

import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F000
import Definitions.Def_StochLean_Probability_Process_Path_Cadlag_F001
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.WithTop

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Separated samples of a cadlag path cannot accumulate in finite time

Infinitely many chronologically ordered samples with a fixed positive consecutive
oscillation must escape every finite horizon. The contradiction uses the actual
finite left limit at a hypothetical accumulation point, not a compactness assumption
about a space of paths.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] {x : ℝ≥0 → E}

namespace IsCadlagPath
theorem _root_.Prove2MeSourceProof.h_8e6db4db0ea19e4e1d9e41fa (hx : IsCadlagPath x)
    {u : ℕ → ℝ≥0} (hu : StrictMono u) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ n, ε ≤ ‖x (u (n + 1)) - x (u n)‖) : Tendsto u atTop atTop := by
  rcases tendsto_atTop_of_monotone hu.monotone with htop | ⟨T, hlim⟩
  · exact htop
  · have hlt (n : ℕ) : u n < T :=
      (hu (Nat.lt_succ_self n)).trans_le (hu.monotone.ge_of_tendsto hlim (n + 1))
    have hT : T ≠ (0 : ℝ≥0) := ne_of_gt ((bot_le : (0 : ℝ≥0) ≤ u 0).trans_lt (hlt 0))
    obtain ⟨y, hy⟩ := hx.2 T hT
    have hwithin : Tendsto u atTop (𝓝[<] T) :=
      tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hlt⟩
    have hxu : Tendsto (fun n ↦ x (u n)) atTop (𝓝 y) := hy.comp hwithin
    have hdiff : Tendsto (fun n ↦ ‖x (u (n + 1)) - x (u n)‖) atTop (𝓝 0) := by
      simpa only [Function.comp_def, sub_self, norm_zero] using
        ((hxu.comp (tendsto_add_atTop_nat 1)).sub hxu).norm
    exact (not_le_of_gt hε (ge_of_tendsto' hdiff hsep)).elim
end IsCadlagPath

end ProbabilityTheory


