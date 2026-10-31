-- Prove2me | Definitions.Def_FastCore_IsMBCC
-- name    : FastCore_IsMBCC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:53.382984+00:00
-- url     : https://prove2.me/theorems/63ac1b2c-ab83-4a37-9a2a-cd168883a8c9
-- title:
--   Maximum Binding Core Constraint
-- statement:
--   Given utilities $\{\pi_i\}_{i\in N}$, a subset $S\subseteq N$ is a **Maximum Binding Core Constraint** (MBCC) if
--
--   $$
--   S\in\operatorname*{arg\,max}_{S'\subseteq N}\ \Bigl(w(S')-\sum_{i\in S'}\pi_i\Bigr).
--   $$
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 4, p.12

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_w

namespace FastCore

/-- `S` is a Maximum Binding Core Constraint for `π` (Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 4, p.12):
`S ∈ argmax_{S' ⊆ N} (w(S') − ∑_{i ∈ S'} πᵢ)`. -/
def IsMBCC {n m : ℕ} (b : Bids n m) (π : Fin n → ℝ) (S : Finset (Fin n)) : Prop :=
  ∀ S', w b S' - ∑ i ∈ S', π i ≤ w b S - ∑ i ∈ S, π i

end FastCore


