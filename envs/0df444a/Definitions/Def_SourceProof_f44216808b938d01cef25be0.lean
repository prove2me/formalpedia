-- Prove2me | Definitions.Def_SourceProof_f44216808b938d01cef25be0
-- name    : SourceProof_f44216808b938d01cef25be0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T19:17:25.442711+00:00
-- url     : https://prove2.me/theorems/b77e85f1-7ca4-4570-8c2e-ff7ee5ceee20
-- title:
--   StochLean source theorem: StochLean.TimePartition.sum_endpointPairStep_eq_sum_selected

import Definitions.Def_StochLean_Analysis_PathVariation_EndpointPairStep_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Endpoint-pair sums on finitely selected cells

A selected time belongs to a left-open, right-closed cell. Once no two
selected times share a cell, the sum over selected times equals exactly
the sum over selected cells. The limit retains both sides of every jump.
-/

@[expose] public section

open Set Finset Filter ProbabilityTheory
open scoped NNReal Topology

namespace StochLean.TimePartition

theorem _root_.Prove2MeSourceProof.h_f44216808b938d01cef25be0 {E : Type*} {T : ℝ≥0} (π : TimePartition T)
    (A : Finset ℝ≥0) (hA : ∀ s ∈ A, s ∈ Ioc 0 T)
    (hsep : ∀ i : Fin π.size, ∀ s ∈ A, ∀ r ∈ A,
      s ∈ Ioc (π.left i) (π.right i) → r ∈ Ioc (π.left i) (π.right i) → s = r)
    (Φ : E → E → ℝ) (x : ℝ≥0 → E) :
    (∑ s ∈ A, π.endpointPairStep Φ x s) =
      ∑ i : Fin π.size, if ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
        then Φ (x (π.left i)) (x (π.right i)) else 0 := by
  classical
  calc
    _ = ∑ s ∈ A, ∑ i : Fin π.size,
        if s ∈ Ioc (π.left i) (π.right i)
          then Φ (x (π.left i)) (x (π.right i)) else 0 := by
      apply sum_congr rfl
      intro s hs
      rw [StochLean.TimePartition.endpointPairStep, if_neg (ne_of_gt (hA s hs).1)]
      simp only [Set.indicator_apply]
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      by_cases he : ∃ s ∈ A, s ∈ Ioc (π.left i) (π.right i)
      · rw [if_pos he]
        obtain ⟨s, hs, hsc⟩ := he
        rw [sum_eq_single s]
        · exact if_pos hsc
        · intro r hr hrs
          apply if_neg
          intro hrc
          exact hrs (hsep i r hr s hs hrc hsc)
        · exact fun hnot ↦ (hnot hs).elim
      · rw [if_neg he]
        apply sum_eq_zero
        intro s hs
        exact if_neg (fun hsc ↦ he ⟨s, hs, hsc⟩)
end StochLean.TimePartition


