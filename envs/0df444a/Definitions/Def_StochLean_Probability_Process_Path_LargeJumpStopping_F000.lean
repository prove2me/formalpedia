-- Prove2me | Definitions.Def_StochLean_Probability_Process_Path_LargeJumpStopping_F000
-- name    : StochLean_Probability_Process_Path_LargeJumpStopping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:41:03.183077+00:00
-- url     : https://prove2.me/theorems/84654a34-e5db-5cef-a292-523d995a33be
-- title:
--   StochLean: Probability.Process.Path.LargeJumpStopping F000

import Definitions.Def_StochLean_Probability_Process_Path_LargeJumpSum_F000
import Definitions.Def_SourceProof_2adad6656f12f977d8bc8198
import Definitions.Def_SourceProof_d6df4f936460d2a881b56ca9
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.NNReal.Basic
import Mathlib.Probability.Process.Stopping
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Stopping and event restriction of the actual large-jump sums

Both cumulative processes commute with stopping on the common cadlag event.
The lifetime need not be a stopping time: this is a path identity. The jump
at a finite stopping endpoint is included, while an infinite lifetime leaves
every finite-time value unchanged. At lifetime zero both cumulative sums
are zero, because their actual index interval excludes the initial atom.

Restriction to a fixed sample event commutes exactly, without measurability
or path regularity assumptions. All four identities hold for an arbitrary
real threshold: each of the two truncation maps sends zero to zero. No
global absolute summability, infinite-time value, or new process selector
is introduced.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω}

private theorem tsum_jump_transform_stoppedProcess (hx : IsCadlagPath (X · ω))
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) :
    (∑' s : Ioc 0 t, φ (jumpProcess (MeasureTheory.stoppedProcess X τ) s ω)) =
      ∑' s : Ioc 0 ((min (t : WithTop ℝ≥0) (τ ω)).untopA), φ (jumpProcess X s ω) := by
  cases hτ : τ ω with
  | top =>
    simp only [WithTop.untopA]
    apply tsum_congr
    intro s
    rw [(_root_.Prove2MeSourceProof.h_2adad6656f12f977d8bc8198 hx) τ s, hτ, if_pos le_top]
  | coe a =>
    simp only [← WithTop.coe_min, WithTop.untopD_coe]
    calc
      _ = ∑' s : Ioc 0 t,
          if (s : ℝ≥0) ≤ a then φ (jumpProcess X s ω) else 0 := by
        apply tsum_congr
        intro s
        rw [(_root_.Prove2MeSourceProof.h_2adad6656f12f977d8bc8198 hx) τ s, hτ]
        simp only [WithTop.coe_le_coe]
        split_ifs <;> simp only [hφ]
      _ = _ := _root_.Prove2MeSourceProof.h_d6df4f936460d2a881b56ca9 (fun s ↦ φ (jumpProcess X s ω)) a t
private theorem tsum_jump_transform_indicator (X : ℝ≥0 → Ω → ℝ)
    (φ : ℝ → ℝ) (hφ : φ 0 = 0) (S : Set Ω) :
    (fun (t : ℝ≥0) ω ↦ ∑' s : Ioc 0 t,
      φ (jumpProcess (fun u ↦ S.indicator (X u)) s ω)) =
      fun t ↦ S.indicator (fun ω ↦ ∑' s : Ioc 0 t, φ (jumpProcess X s ω)) := by
  classical
  funext t ω
  by_cases hS : ω ∈ S
  · simp only [indicator_of_mem hS, jumpProcess, Pi.sub_apply, leftLimitProcess]
  · rw [indicator_of_notMem hS]
    have hj (s : ℝ≥0) : jumpProcess (fun u ↦ S.indicator (X u)) s ω = 0 := by
      simp only [jumpProcess, Pi.sub_apply, leftLimitProcess, indicator_of_notMem hS]
      rw [(continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : ℝ))).continuousWithinAt.leftLim_eq]
      simp only [ite_self, sub_self]
    simp only [hj, hφ, tsum_zero]
variable {mΩ : MeasurableSpace Ω} {P : Measure Ω}

end ProbabilityTheory


