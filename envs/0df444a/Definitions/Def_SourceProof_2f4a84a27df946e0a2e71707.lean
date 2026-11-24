-- Prove2me | Definitions.Def_SourceProof_2f4a84a27df946e0a2e71707
-- name    : SourceProof_2f4a84a27df946e0a2e71707
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:32.749806+00:00
-- url     : https://prove2.me/theorems/3f0c9ece-5025-43d2-a287-409ddfc99baf
-- title:
--   StochLean source theorem: StochLean.stronglyMeasurable_integral_kernel_of_finite_fibers

import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Integrals against kernels with finite fibers

Fiberwise finite mass need not have a uniform bound in the sample parameter.
We truncate by measurable mass levels and use eventual equality at each sample.
-/

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory Function
open scoped ENNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_2f4a84a27df946e0a2e71707
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Kernel α β) (hκ : ∀ a, IsFiniteMeasure (κ a))
    {f : α → β → E} (hf : StronglyMeasurable (uncurry f)) :
    StronglyMeasurable fun a ↦ ∫ b, f a b ∂κ a := by
  classical
  have hm (n : ℕ) : MeasurableSet {a | κ a univ ≤ (n : ℝ≥0∞)} :=
    measurableSet_le (κ.measurable_coe MeasurableSet.univ) measurable_const
  let κn (n : ℕ) : Kernel α β := Kernel.piecewise (hm n) κ 0
  have hκn (n : ℕ) : IsFiniteKernel (κn n) := by
    refine ⟨⟨(n : ℝ≥0∞), by finiteness, fun a ↦ ?_⟩⟩
    change (if a ∈ {a | κ a univ ≤ (n : ℝ≥0∞)} then κ a else 0) univ ≤ _
    split_ifs with ha
    · exact ha
    · simp
  apply stronglyMeasurable_of_tendsto (f := fun n a ↦ ∫ b, f a b ∂κn n a) atTop
  · intro n
    let : IsFiniteKernel (κn n) := hκn n
    exact hf.integral_kernel_prod_right
  · apply tendsto_pi_nhds.mpr
    intro a
    let : IsFiniteMeasure (κ a) := hκ a
    obtain ⟨N, hN⟩ := exists_nat_gt ((κ a).real univ)
    have hmass : κ a univ ≤ (N : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top (κ a) univ)]
      exact (ENNReal.ofReal_le_ofReal hN.le).trans_eq (by simp)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : κ a univ ≤ (n : ℝ≥0∞) := hmass.trans (Nat.cast_le.mpr hn)
    simp only [κn, Kernel.piecewise_apply, mem_ofPred_eq, if_pos hle]
end StochLean


