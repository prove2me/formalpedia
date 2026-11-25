-- Prove2me | Definitions.Def_SourceProof_564697e1323307dfe37a6d6d
-- name    : SourceProof_564697e1323307dfe37a6d6d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:46:58.295444+00:00
-- url     : https://prove2.me/theorems/3e097d6d-dcd2-418e-b66c-eb8f90bf1451
-- title:
--   StochLean source theorem: StochLean.LocallyFinitePartition.range_stop_restrict

import Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F005
import Definitions.Def_StochLean_Analysis_PathVariation_Stopping_F000
import Definitions.Def_SourceProof_22d80a2190f136747d0e9643
import Definitions.Def_SourceProof_939d8318cd36045b63ec8877

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Exact transport between finite and infinite partition restrictions

Stopping an enclosing finite restriction repeats its terminal endpoint. Direct restriction
deduplicates that endpoint. Endpoint-set invariance proves exact equality of their sums.
-/

@[expose] public section

open Set
open scoped NNReal

namespace StochLean.LocallyFinitePartition

theorem _root_.Prove2MeSourceProof.h_564697e1323307dfe37a6d6d (π : LocallyFinitePartition) {s T : ℝ≥0} (hs : s ≤ T) :
    Set.range ((π.restrict T).stop s hs).point = Set.range (π.restrict s).point := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    apply ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 π) s _).mpr
    change min ((π.restrict T).point i) s = s ∨
      min ((π.restrict T).point i) s ∈ π.points ∧ min ((π.restrict T).point i) s ≤ s
    by_cases hi : (π.restrict T).point i ≤ s
    · rw [min_eq_left hi]
      rcases ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 π) T _).mp ⟨i, rfl⟩ with hT | ⟨hp, _⟩
      · exact Or.inl (le_antisymm hi (hs.trans_eq hT.symm))
      · exact Or.inr ⟨hp, hi⟩
    · exact Or.inl (min_eq_right (le_of_not_ge hi))
  · intro hx
    rcases ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 π) s x).mp hx with hxs | ⟨hx, hxs⟩
    · subst x
      refine ⟨Fin.last (π.restrict T).size, ?_⟩
      change min ((π.restrict T).point (Fin.last _)) s = s
      rw [(π.restrict T).last_eq_horizon, min_eq_right hs]
    · obtain ⟨i, hi⟩ := ((_root_.Prove2MeSourceProof.h_22d80a2190f136747d0e9643 π) T x).mpr (Or.inr ⟨hx, hxs.trans hs⟩)
      exact ⟨i, by change min ((π.restrict T).point i) s = x; rw [hi, min_eq_left hxs]⟩
end StochLean.LocallyFinitePartition


