-- Prove2me | Definitions.Def_SourceProof_f17e21373c03eb2c377aaee1
-- name    : SourceProof_f17e21373c03eb2c377aaee1
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:07:59.731063+00:00
-- url     : https://prove2.me/theorems/dac388b3-5f0d-4660-8080-2a477c3ea865
-- title:
--   StochLean source theorem: ContinuousWithinAt.tendsto_leftLim_nhdsGT

import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Right limits of the strict-left-limit function -/

@[expose] public section

open Function Filter Set
open scoped Topology

variable {α E : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [NoMaxOrder α] [TopologicalSpace E] [T3Space E]

namespace ContinuousWithinAt

theorem _root_.Prove2MeSourceProof.h_f17e21373c03eb2c377aaee1 {f : α → E} {a : α}
    (h : ContinuousWithinAt f (Ici a) a) :
    Tendsto f.leftLim (𝓝[>] a) (𝓝 (f a)) := by
  apply (closed_nhds_basis (f a)).tendsto_right_iff.mpr
  rintro s ⟨hs, hc⟩
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp (h hs)
  filter_upwards [Ioo_mem_nhdsGT hu] with b hb
  apply hc.mem_of_mapClusterPt ((mapClusterPt_leftLim f b).mono nhdsWithin_le_nhds)
  filter_upwards [Ioo_mem_nhds hb.1 hb.2] with c hc
  exact hsub ⟨hc.1.le, hc.2⟩
end ContinuousWithinAt


