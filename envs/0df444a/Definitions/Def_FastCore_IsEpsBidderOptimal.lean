-- Prove2me | Definitions.Def_FastCore_IsEpsBidderOptimal
-- name    : FastCore_IsEpsBidderOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:53.137212+00:00
-- url     : https://prove2.me/theorems/b718d082-7513-44f0-a126-2460caddd291
-- title:
--   $\epsilon$-bidder optimal core point
-- statement:
--   A utility vector $\{\pi_i\}_{i\in N}$ is **$\epsilon$-bidder optimal** if
--
--   1. $\pi$ is in the core, and
--   2. there is no other core point $\pi'$ with $\pi'_i\ge\pi_i$ for every bidder $i$ and $\pi'_j>\pi_j+\epsilon$ for at least one bidder $j$.
--
--   This is the output guarantee of Algorithm 1.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 3, p.12

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_InCore

namespace FastCore

/-- `π` is `ε`-bidder optimal (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 3, p.12): `π` is in the core, and no other core
point `π'` has `π'ᵢ ≥ πᵢ` for every bidder and `π'ⱼ > πⱼ + ε` for at least one bidder `j`. -/
def IsEpsBidderOptimal {n m : ℕ} (b : Bids n m) (ε : ℝ) (π : Fin n → ℝ) : Prop :=
  InCore b π ∧ ¬ ∃ π', InCore b π' ∧ (∀ i, π i ≤ π' i) ∧ ∃ j, π j + ε < π' j

end FastCore


