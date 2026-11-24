-- Prove2me | Definitions.Def_SourceProof_78da39830a86073c1a81eb5d
-- name    : SourceProof_78da39830a86073c1a81eb5d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:37.550904+00:00
-- url     : https://prove2.me/theorems/298a5e4a-54f9-4dd8-837f-f25879444457
-- title:
--   StochLean source theorem: TendstoUniformlyOn.exists_tendsto_of_exists_tendsto

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Existence of a limit passes through uniform convergence

Completeness constructs the limit of the approximants' limits; it is not an
additional convergence hypothesis in the conclusion.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {α E : Type*} [MetricSpace E] [CompleteSpace E]
  {F : ℕ → α → E} {f : α → E} {s : Set α} {q : Filter α}

namespace TendstoUniformlyOn
theorem _root_.Prove2MeSourceProof.h_78da39830a86073c1a81eb5d [q.NeBot]
    (h : TendstoUniformlyOn F f atTop s) (hq : q ≤ 𝓟 s)
    (hF : ∀ n, ∃ y, Tendsto (F n) q (𝓝 y)) : ∃ y, Tendsto f q (𝓝 y) := by
  choose L hL using hF
  have hc : CauchySeq L := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp h.uniformCauchySeqOn
      (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn ↦ ?_⟩
    have hd : dist (L m) (L n) ≤ ε / 2 := by
      apply le_of_tendsto ((hL m).dist (hL n))
      filter_upwards [le_principal_iff.mp hq] with x hx
      exact (hN m hm n hn x hx).le
    exact hd.trans_lt (half_lt_self hε)
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨y, (h.tendstoUniformlyOnFilter.mono_right hq).tendsto_of_eventually_tendsto
    (Eventually.of_forall hL) hy⟩
end TendstoUniformlyOn


