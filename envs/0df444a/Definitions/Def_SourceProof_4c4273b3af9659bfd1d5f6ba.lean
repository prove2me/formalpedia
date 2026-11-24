-- Prove2me | Definitions.Def_SourceProof_4c4273b3af9659bfd1d5f6ba
-- name    : SourceProof_4c4273b3af9659bfd1d5f6ba
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:14:11.234678+00:00
-- url     : https://prove2.me/theorems/64dd739e-6a4d-4633-9bef-b4189e6dd048
-- title:
--   StochLean source theorem: StochLean.TimePartition.eventually_separate_finite_times

import Definitions.Def_SourceProof_f81d4c461f298be40223e563

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Fine partitions separate any prescribed finite collection of times -/

@[expose] public section

open Set Filter
open scoped NNReal Topology

namespace StochLean.TimePartition

theorem _root_.Prove2MeSourceProof.h_4c4273b3af9659bfd1d5f6ba {T : ℝ≥0} {π : ℕ → TimePartition T}
    (hmesh : Tendsto (fun n ↦ ((π n).mesh : ℝ)) atTop (𝓝 0)) (A : Finset ℝ≥0) :
    ∀ᶠ n in atTop, ∀ i : Fin (π n).size, ∀ s ∈ A, ∀ r ∈ A,
      s ∈ Ioc ((π n).left i) ((π n).right i) →
        r ∈ Ioc ((π n).left i) ((π n).right i) → s = r := by
  have hdist : ∀ᶠ n in atTop, ∀ s ∈ A, ∀ r ∈ A, s ≠ r →
      ((π n).mesh : ℝ) < dist s r := by
    apply (eventually_all_finset A).mpr
    intro s _
    apply (eventually_all_finset A).mpr
    intro r _
    by_cases hsr : s = r
    · exact Eventually.of_forall (fun _ h ↦ (h hsr).elim)
    · exact (hmesh.eventually_lt_const (dist_pos.mpr hsr)).mono (fun _ h _ ↦ h)
  filter_upwards [hdist] with n hn
  intro i s hs r hr hsc hrc
  by_contra hne
  have hbound := (_root_.Prove2MeSourceProof.h_f81d4c461f298be40223e563 (π n)) ⟨hsc.1.le, hsc.2⟩ ⟨hrc.1.le, hrc.2⟩
  exact (not_lt_of_ge hbound) (hn s hs r hr hne)
end StochLean.TimePartition


