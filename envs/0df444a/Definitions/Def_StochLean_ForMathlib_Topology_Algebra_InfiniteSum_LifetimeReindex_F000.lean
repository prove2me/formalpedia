-- Prove2me | Definitions.Def_StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000
-- name    : StochLean_ForMathlib_Topology_Algebra_InfiniteSum_LifetimeReindex_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T16:06:41.289697+00:00
-- url     : https://prove2.me/theorems/9148f950-a6db-4c75-8190-8aeb88fde811
-- title:
--   StochLean: ForMathlib.Topology.Algebra.InfiniteSum.LifetimeReindex F000

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Order.WithBot

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

private theorem exists_lifetime_support_embedding {α ι E : Type*} [Zero E]
    {f : α → E} {g : ι → E} {τ : ι → WithTop α}
    (hdisj : ∀ i j (t : α), τ i = (t : WithTop α) → τ j = (t : WithTop α) → i = j)
    (htop : ∀ i, τ i = ⊤ → g i = 0)
    (hcoe : ∀ i (t : α), τ i = (t : WithTop α) → g i = f t) :
    ∃ e : support g → α, Injective e ∧
      (∀ i : support g, τ i = (e i : WithTop α)) ∧ (∀ i, f (e i) = g i) := by
  classical
  have hfinite (i : support g) : ∃ t : α, τ i = (t : WithTop α) := by
    have hn : τ i ≠ ⊤ := fun h ↦ i.property (htop i h)
    obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hn
    exact ⟨t, ht.symm⟩
  choose e he using hfinite
  refine ⟨e, ?_, he, fun i ↦ (hcoe i (e i) (he i)).symm⟩
  intro i j hij
  apply Subtype.ext
  exact hdisj i j (e i) (he i)
    ((he j).trans (congrArg (fun t : α ↦ (t : WithTop α)) hij.symm))
end StochLean


