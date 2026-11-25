-- Prove2me | Definitions.Def_SourceProof_f663a9831488630e6f3e2684
-- name    : SourceProof_f663a9831488630e6f3e2684
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T00:30:44.479895+00:00
-- url     : https://prove2.me/theorems/abdaf138-0f69-44a0-a165-be6913afa0ac
-- title:
--   StochLean source theorem: StochLean.sum_intervalIncrement_congr

import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F002
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F003
import Definitions.Def_StochLean_Analysis_PathVariation_Basic_F005
import Definitions.Def_SourceProof_81a7a13dc7d130704fab006e
import Mathlib.Tactic.Order

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Representation independence of finite interval integration

The integrator is an arbitrary real-valued function. A zero finite linear
combination of half-open interval indicators has zero increment integral.
This is the deterministic algebra behind Protter's elementary integral.
-/

@[expose] public section

open Filter Finset Set
open scoped NNReal Topology BigOperators

namespace StochLean


theorem _root_.Prove2MeSourceProof.h_f663a9831488630e6f3e2684 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a b : ι → ℝ≥0) (c : ι → ℝ) (a' b' : κ → ℝ≥0) (c' : κ → ℝ)
    (hab : ∀ i, a i ≤ b i) (hab' : ∀ j, a' j ≤ b' j)
    (heq : ∀ t : ℝ≥0, 0 < t →
      (∑ i, if a i < t ∧ t ≤ b i then c i else 0) =
        ∑ j, if a' j < t ∧ t ≤ b' j then c' j else 0)
    (f : ℝ≥0 → ℝ) :
    (∑ i, c i * (f (b i) - f (a i))) = ∑ j, c' j * (f (b' j) - f (a' j)) := by
  classical
  have hz := _root_.Prove2MeSourceProof.h_81a7a13dc7d130704fab006e
    (Sum.elim a a') (Sum.elim b b') (Sum.elim c (fun j ↦ -c' j))
    (fun i ↦ by cases i with | inl i => exact hab i | inr j => exact hab' j)
    (fun t ht ↦ by
      rw [Fintype.sum_sum_type]
      change (∑ i, if a i < t ∧ t ≤ b i then c i else 0) +
        (∑ j, if a' j < t ∧ t ≤ b' j then -c' j else 0) = 0
      have hneg (j : κ) : (if a' j < t ∧ t ≤ b' j then -c' j else 0) =
          -(if a' j < t ∧ t ≤ b' j then c' j else 0) := by
        split_ifs <;> simp
      simp only [hneg, sum_neg_distrib]
      rw [heq t ht, add_neg_cancel]) f
  simpa only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib,
    add_neg_eq_zero] using hz
end StochLean


