-- Prove2me | Definitions.Def_SourceProof_bf9c1f28ce44b7204ce64183
-- name    : SourceProof_bf9c1f28ce44b7204ce64183
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:43.41854+00:00
-- url     : https://prove2.me/theorems/ab28cc3b-e85d-4028-9cf7-a80c79f88928
-- title:
--   StochLean source theorem: ProbabilityTheory.tendstoUniformly_min_of_tendsto_nhdsGE

import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.UniformSpace.UniformConvergence

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Uniform path convergence when stopping times approach from the right

Right continuity at the limiting endpoint controls all intermediate values.
The stopped functions converge uniformly on the entire half-line, despite
possible jumps elsewhere in the original path.
-/

@[expose] public section

open Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

theorem _root_.Prove2MeSourceProof.h_bf9c1f28ce44b7204ce64183 {E : Type*} [PseudoMetricSpace E]
    {x : ℝ≥0 → E} {a : ℝ≥0} {v : ℕ → ℝ≥0}
    (hx : ContinuousWithinAt x (Ici a) a) (hv : Tendsto v atTop (𝓝[≥] a)) :
    TendstoUniformly (fun n t ↦ x (min (v n) t)) (fun t ↦ x (min a t)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hmod⟩ := Metric.continuousWithinAt_iff.mp hx ε hε
  have hdist := Metric.tendsto_nhds.mp (hv.mono_right nhdsWithin_le_nhds) δ hδ
  filter_upwards [hv.eventually self_mem_nhdsWithin, hdist] with n hn hdn
  intro t
  have han : a ≤ v n := hn
  by_cases hta : t ≤ a
  · simp only [min_eq_right hta, min_eq_right (hta.trans han), dist_self]
    exact hε
  · have hat : a ≤ t := (lt_of_not_ge hta).le
    have hmin : a ≤ min (v n) t := le_min han hat
    have hd : dist (min (v n) t) a ≤ dist (v n) a := by
      rw [NNReal.dist_eq, NNReal.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast hmin)),
        abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast han))]
      exact sub_le_sub_right (by exact_mod_cast min_le_left (v n) t) _
    have hb := hmod hmin (hd.trans_lt hdn)
    simpa only [min_eq_left hat, dist_comm] using hb
end ProbabilityTheory


