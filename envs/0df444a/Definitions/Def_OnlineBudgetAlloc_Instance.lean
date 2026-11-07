-- Prove2me | Definitions.Def_OnlineBudgetAlloc_Instance
-- name    : OnlineBudgetAlloc_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:29:37.380638+00:00
-- url     : https://prove2.me/theorems/19b02e74-968d-4c85-a8d8-2901d96ea735
-- title:
--   An instance of online budgeted allocation: budgets $B_j$ and bids $b_{ij}$
-- statement:
--   An instance of **online budgeted allocation** consists of $m$ items and $N$ advertisers. Advertiser $j$ has a budget $B_j$, known offline, and places a bid $b_{ij}$ on item $i$. Items arrive one at a time; when item $i$ arrives its bids $(b_{ij})_j$ are revealed.
--
--   This is the input of every statement in the mission: the goal theorem asks for an instance with all $B_j = 1$ and all bids in $\{0, \tfrac12, \tfrac34, 1\}$.
--
--   **Formalization Note** Items are indexed by $\{0,\dots,m-1\}$ and advertisers by $\{0,\dots,N-1\}$. The paper calls the number of items $M$ but reuses $M$ for $2N/3$ from §2 on, so the item count is written $m$. The paper's standing assumptions $B_j \ge 0$ and $b_{ij} \ge 0$ are not part of the structure; they hold for every instance the theorems are about.
-- source:
--   Panigrahi, Zhang, The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1

import Mathlib

namespace OnlineBudgetAlloc

/-- An instance of **online budgeted allocation** with `N` advertisers and `m` items
(Panigrahi–Zhang, *The Competitive Ratio of Online Budgeted Allocation is Strictly Smaller than 1-1/e*, arXiv:2610.41136 (held version, sha256 913d8f02…), §1, p.1). Advertiser `j` has a budget `B j`, known offline, and places the bid `b i j`
on item `i`.

**Formalization Note** Items are `Fin m` and advertisers `Fin N`, both zero-based. The paper calls
the number of items `M`; from §2 on it reuses `M` for `2N/3`, so the item count is `m` here. The
paper's standing assumptions `B j ≥ 0` and `b i j ≥ 0` are not bundled into the structure; they
hold for every instance the theorems of this mission are about (unit budgets, bids in
`{0, 1/2, 3/4, 1}`). -/
structure Instance (N m : ℕ) where
  /-- The budget `B_j` of advertiser `j`. -/
  B : Fin N → ℝ
  /-- The bid `b_ij` of advertiser `j` on item `i`. -/
  b : Fin m → Fin N → ℝ

end OnlineBudgetAlloc


