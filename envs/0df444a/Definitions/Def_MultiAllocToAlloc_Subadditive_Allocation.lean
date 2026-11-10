-- Prove2me | Definitions.Def_MultiAllocToAlloc_Subadditive_Allocation
-- name    : MultiAllocToAlloc_Subadditive_Allocation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T18:09:15.553667+00:00
-- url     : https://prove2.me/theorems/40df940e-a977-4c0d-ac51-1f1273213d6b
-- title:
--   Allocations and d-multi-allocations
-- statement:
--   Agents are `Fin n` and items `Fin m`; a family of bundles is `A : Fin n → Finset (Fin m)`. It is an **allocation** when the bundles are pairwise disjoint ($A_i\cap A_j=\emptyset$ for $i\neq j$); it need not cover all items. It is a **$d$-multi-allocation** when every item belongs to at most $d$ of the bundles: $|\{i : e\in A_i\}|\le d$ for every item $e$ (p. 1).
-- source:
--   Feige, arXiv:2506.21493v1, §1, p. 1

import Mathlib

namespace MultiAllocToAlloc.Subadditive

/-- An allocation (Feige, arXiv:2506.21493v1, §1, p. 1): bundles `A i` (agents `Fin n`,
items `Fin m`) that are pairwise disjoint. It need not cover all items. -/
def IsAllocation {n m : ℕ} (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j : Fin n, i ≠ j → Disjoint (A i) (A j)

/-- A `d`-multi-allocation (Feige, arXiv:2506.21493v1, §1, p. 1): possibly intersecting bundles
`A i` such that every item belongs to at most `d` of them. -/
def IsMultiAllocation {n m : ℕ} (d : ℕ) (A : Fin n → Finset (Fin m)) : Prop :=
  ∀ e : Fin m, (Finset.univ.filter (fun i : Fin n => e ∈ A i)).card ≤ d

end MultiAllocToAlloc.Subadditive


