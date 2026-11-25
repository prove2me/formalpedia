-- Prove2me | Definitions.Def_SourceProof_6d08683551c02469b0aeb8c7
-- name    : SourceProof_6d08683551c02469b0aeb8c7
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:05:39.376809+00:00
-- url     : https://prove2.me/theorems/12a4b2e7-9a5b-5e7b-8a73-6dcce81bc59b
-- title:
--   StochLean source theorem: StochLean.norm_firstOrderRemainder_le

import Definitions.Def_StochLean_Analysis_PathVariation_StieltjesIntegralRiemann_F000
import Definitions.Def_StochLean_Analysis_PathVariation_UniformPartition_F001
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # C1 change of variables along a continuous finite-variation path

The first-order remainders are bounded by their derivative oscillation times
the path variation. Actual left Riemann sums identify the Stieltjes integral.
The increment formula excludes the separately owned source initial term.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped NNReal Topology

namespace StochLean

theorem _root_.Prove2MeSourceProof.h_6d08683551c02469b0aeb8c7 {φ φ' : ℝ → ℝ} (hφ : ∀ z, HasDerivAt φ (φ' z) z)
    {a b C : ℝ} (hb : ∀ z ∈ uIcc a b, ‖φ' z - φ' a‖ ≤ C) :
    ‖φ b - φ a - φ' a * (b - a)‖ ≤ C * ‖b - a‖ := by
  have hd (z : ℝ) : HasDerivAt (fun u ↦ φ u - φ' a * u) (φ' z - φ' a) z := by
    have hl : HasDerivAt (fun u ↦ φ' a * u) (φ' a) z := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id z).const_mul (φ' a)
    exact (hφ z).sub hl
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc a b) ↦ (hd z).hasDerivWithinAt) hb (convex_uIcc a b)
    left_mem_uIcc right_mem_uIcc
  convert h using 1
  congr 1
  ring
end StochLean


