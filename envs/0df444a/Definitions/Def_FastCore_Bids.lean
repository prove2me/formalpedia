-- Prove2me | Definitions.Def_FastCore_Bids
-- name    : FastCore_Bids
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:10.658987+00:00
-- url     : https://prove2.me/theorems/e0f14508-f12a-493b-9d4e-e76aa61e1cec
-- title:
--   Bid profile of $n$ bidders on $m$ items
-- statement:
--   A combinatorial auction has $n$ bidders $N=\{1,\dots,n\}$ and $m$ items. A **bid profile** $\{b_i\}_{i\in N}$ assigns to each bidder $i$ a valuation function $b_i$, which gives a real value $b_i(A)$ to every bundle $A\subseteq[m]$.
--
--   This is the input of every statement in the mission. The paper's assumptions on the values are recorded separately as `IsBidProfile`.
--
--   **Formalization Note** Bidders are `Fin n` and bundles are `Finset (Fin m)`. The cases $n=0$ and $m=0$ are not excluded.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10

import Mathlib

namespace FastCore

/-- A bid profile of `n` bidders on `m` items: `b i A` is the value `bᵢ(A)` that bidder `i` declares
for the bundle `A` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10).

**Formalization Note.** The bidders `N = {1,…,n}` are `Fin n` and `2^[m]` is `Finset (Fin m)`;
`n = 0` and `m = 0` are allowed. The assumptions on the values are `IsBidProfile`. -/
abbrev Bids (n m : ℕ) : Type := Fin n → Finset (Fin m) → ℝ

end FastCore


