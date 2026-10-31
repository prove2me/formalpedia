-- Prove2me | Definitions.Def_FastCore_IsBidProfile
-- name    : FastCore_IsBidProfile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:57.659147+00:00
-- url     : https://prove2.me/theorems/e189d332-d8ea-4552-bf59-0aed25e6d508
-- title:
--   Normalized bids with values in $[0,1]$
-- statement:
--   A bid profile $\{b_i\}_{i\in N}$ satisfies the paper's standing assumption if every valuation is normalized and all values lie in the unit interval:
--
--   $$
--   b_i(\emptyset)=0\quad\text{and}\quad 0\le b_i(A)\le 1\qquad\text{for all } i\in N,\ A\subseteq[m].
--   $$
--
--   No monotonicity is assumed. The upper bound $1$ is what makes the bisection interval $[0,1]$ of Core-Search sufficient.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10

import Mathlib
import Definitions.Def_FastCore_Bids

namespace FastCore

/-- The standing assumption on bids (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, §2, p.10): "valuation functions are normalized so
that `bᵢ(∅) = 0`, and all values are in `[0,1]`". No monotonicity is assumed. -/
def IsBidProfile {n m : ℕ} (b : Bids n m) : Prop :=
  (∀ i, b i ∅ = 0) ∧ ∀ i A, 0 ≤ b i A ∧ b i A ≤ 1

end FastCore


