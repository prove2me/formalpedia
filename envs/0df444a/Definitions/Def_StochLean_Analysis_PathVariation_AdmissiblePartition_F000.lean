-- Prove2me | Definitions.Def_StochLean_Analysis_PathVariation_AdmissiblePartition_F000
-- name    : StochLean_Analysis_PathVariation_AdmissiblePartition_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:18.968524+00:00
-- url     : https://prove2.me/theorems/276a3d20-0927-4d79-bf86-2624434f1e55
-- title:
--   StochLean: Analysis.PathVariation.AdmissiblePartition F000

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Locally finite deterministic partitions and finite-horizon restriction

An infinite partition is stored as its set of endpoints. Restriction to `[0,T]`
keeps every original endpoint in that interval and adds only `T`. Its sorted
enumeration belongs to the same finite `TimePartition` owner used by random
partitions. Admissibility uses the maximum adjacent gap, not the insufficient
nearest-neighbor mesh printed in Klenke 21.56; see the source-correction ledger.
-/

@[expose] public section

open Filter Set Finset
open scoped NNReal ENNReal Topology

namespace StochLean

namespace TimePartition

/-- Ordered enumeration of an endpoint set, including the singleton case `T=0`. -/
noncomputable def ofFinset {T : ℝ≥0} (s : Finset ℝ≥0)
    (h0 : 0 ∈ s) (hT : T ∈ s) (hb : ∀ x ∈ s, x ≤ T) : TimePartition T := by
  have hc : s.card = s.card - 1 + 1 :=
    (Nat.sub_add_cancel (card_pos.mpr ⟨0, h0⟩)).symm
  let e := s.orderEmbOfFin hc
  refine ⟨s.card - 1, e, e.monotone, ?_, ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, e i = 0 := by
      change 0 ∈ Set.range (s.orderEmbOfFin hc)
      rw [s.range_orderEmbOfFin hc]
      exact h0
    exact le_antisymm ((e.monotone (Fin.zero_le i)).trans_eq hi) bot_le
  · apply le_antisymm (hb _ (s.orderEmbOfFin_mem hc _))
    obtain ⟨i, hi⟩ : ∃ i, e i = T := by
      change T ∈ Set.range (s.orderEmbOfFin hc)
      rw [s.range_orderEmbOfFin hc]
      exact hT
    exact hi ▸ e.monotone (Fin.le_last i)
end TimePartition

namespace LocallyFinitePartition

end LocallyFinitePartition

end StochLean


