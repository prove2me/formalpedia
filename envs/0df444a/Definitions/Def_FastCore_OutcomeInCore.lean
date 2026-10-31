-- Prove2me | Definitions.Def_FastCore_OutcomeInCore
-- name    : FastCore_OutcomeInCore
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:10.449994+00:00
-- url     : https://prove2.me/theorems/e684cfbc-1fd2-4f7f-9fc3-4de932e70c7c
-- title:
--   Core outcome
-- statement:
--   An outcome $\{(x_i,p_i)\}_{i\in N}$ is **in the core** if $x$ is an allocation, $p_i\ge0$ for each bidder, and its utilities $\pi_i=b_i(x_i)-p_i$ and $\pi_0=\sum_{i\in N}p_i$ are non-negative and satisfy
--
--   $$
--   \pi_0\ \ge\ w(S)-\sum_{i\in S}\pi_i\qquad\text{for all } S\subseteq N. \tag{2}
--   $$
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 2 and eq. (2), p.11

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_w
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

open ComplementFreeCA.CFRounding (IsAllocation welfare)

namespace FastCore

/-- The outcome `(x, p)` is in the core (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 2 and eq. (2), p.11): `x` is an
allocation, the payments are non-negative, and its utilities `πᵢ = bᵢ(xᵢ) − pᵢ`, `π₀ = ∑ᵢ pᵢ` are
non-negative and satisfy `π₀ ≥ w(S) − ∑_S πᵢ` for every `S ⊆ N`. (`π₀ ≥ 0` follows from `p ≥ 0`.) -/
def OutcomeInCore {n m : ℕ} (b : Bids n m) (x : Fin n → Finset (Fin m)) (p : Fin n → ℝ) : Prop :=
  IsAllocation x ∧ (∀ i, 0 ≤ p i) ∧ (∀ i, 0 ≤ b i (x i) - p i) ∧
    ∀ S, w b S - ∑ i ∈ S, (b i (x i) - p i) ≤ ∑ i, p i

end FastCore


