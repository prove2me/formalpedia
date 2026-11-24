-- Prove2me | Definitions.Def_SourceProof_74a6d27af8d8dbe7c2f7b734
-- name    : SourceProof_74a6d27af8d8dbe7c2f7b734
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:13:12.261284+00:00
-- url     : https://prove2.me/theorems/57896966-5a2c-4491-8187-a6f9a8c8b7ee
-- title:
--   StochLean source theorem: StochLean.tsum_eq_tsum_of_disjoint_finite_lifetimes

import Batteries.Tactic.OpenPrivate
import Definitions.Def_StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000

open private exists_lifetime_support_embedding from Definitions.Def_StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000
/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Reindexing sums along disjoint finite lifetime graphs

Only the values at finite lifetimes are used. Infinite lifetimes contribute
zero and may be repeated. The sum identity needs no summability hypothesis;
absolute summability is separately used for quantitative partial-sum bounds.
No new lifetime evaluation or sum owner is introduced.
-/

@[expose] public section

open Function Set

namespace StochLean


theorem _root_.Prove2MeSourceProof.h_74a6d27af8d8dbe7c2f7b734 {α ι : Type*}
    {f : α → ℝ} {g : ι → ℝ} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t)
    (hcover : ∀ t, f t ≠ 0 → ∃ i, τ i = (t : WithTop α)) :
    (∑' t, f t) = ∑' i, g i := by
  classical
  obtain ⟨e, he, hτe, hfe⟩ := exists_lifetime_support_embedding hdisj htop hcoe
  apply tsum_eq_tsum_of_ne_zero_bij e he _ hfe
  intro t ht
  obtain ⟨i, hi⟩ := hcover t ht
  have hgi : g i ≠ 0 := by rwa [hcoe i t hi]
  refine ⟨⟨i, hgi⟩, ?_⟩
  exact WithTop.coe_injective ((hτe ⟨i, hgi⟩).symm.trans hi)
end StochLean


