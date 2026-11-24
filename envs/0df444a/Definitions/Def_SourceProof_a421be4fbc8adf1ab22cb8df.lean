-- Prove2me | Definitions.Def_SourceProof_a421be4fbc8adf1ab22cb8df
-- name    : SourceProof_a421be4fbc8adf1ab22cb8df
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:00:41.082882+00:00
-- url     : https://prove2.me/theorems/6d49d9f8-53c5-4f8b-9517-b63e5f785090
-- title:
--   StochLean source theorem: ProbabilityTheory.indicator_lifetime_le_sub_eq_window

import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.LeftRightLim

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Finite jump removal with bounded residual estimates

Only a fixed finite family of lifetime steps is removed. Its coefficients need not have
an integrable random jump count. A pathwise truncation by the original increment bound
is made before any conditional expectation is taken; no interchange of `min` and
conditional expectation is asserted.
-/

@[expose] public section

open Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω ι : Type*}

theorem _root_.Prove2MeSourceProof.h_a421be4fbc8adf1ab22cb8df (τ : Ω → WithTop ℝ≥0) (Z : Ω → ℝ)
    {t u : ℝ≥0} (htu : t ≤ u) (ω : Ω) :
    {v | τ v ≤ (u : WithTop ℝ≥0)}.indicator Z ω -
      {v | τ v ≤ (t : WithTop ℝ≥0)}.indicator Z ω =
        {v | (t : WithTop ℝ≥0) < τ v ∧ τ v ≤ (u : WithTop ℝ≥0)}.indicator Z ω := by
  classical
  simp only [indicator_apply, mem_ofPred_eq]
  by_cases ht : τ ω ≤ (t : WithTop ℝ≥0)
  · have hu := ht.trans (WithTop.coe_le_coe.mpr htu)
    simp only [ht, hu, not_lt_of_ge ht, false_and, if_true, if_false, sub_self]
  · simp only [ht, lt_of_not_ge ht, true_and, if_false, sub_zero]
end ProbabilityTheory


