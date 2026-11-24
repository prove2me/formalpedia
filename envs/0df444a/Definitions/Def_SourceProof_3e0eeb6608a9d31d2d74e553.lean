-- Prove2me | Definitions.Def_SourceProof_3e0eeb6608a9d31d2d74e553
-- name    : SourceProof_3e0eeb6608a9d31d2d74e553
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:33.091397+00:00
-- url     : https://prove2.me/theorems/38702dac-12f2-4f3f-9a74-8f46dcaa6de0
-- title:
--   StochLean source theorem: TendstoUniformlyOn.tendsto_limit_values

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform convergence controls the values of existing filter limits -/

@[expose] public section

open Filter Set
open scoped Topology

namespace TendstoUniformlyOn
theorem _root_.Prove2MeSourceProof.h_3e0eeb6608a9d31d2d74e553 {α E ι : Type*} [MetricSpace E]
    {F : ι → α → E} {f : α → E} {s : Set α} {p : Filter ι} {q : Filter α} [q.NeBot]
    {L : ι → E} {y : E} (h : TendstoUniformlyOn F f p s) (hq : q ≤ 𝓟 s)
    (hF : ∀ i, Tendsto (F i) q (𝓝 (L i))) (hf : Tendsto f q (𝓝 y)) :
    Tendsto L p (𝓝 y) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h (ε / 2) (half_pos hε)] with i hi
  have hd : dist y (L i) ≤ ε / 2 := by
    apply le_of_tendsto (hf.dist (hF i))
    filter_upwards [le_principal_iff.mp hq] with x hx
    exact (hi x hx).le
  rw [dist_comm]
  exact hd.trans_lt (half_lt_self hε)
end TendstoUniformlyOn


