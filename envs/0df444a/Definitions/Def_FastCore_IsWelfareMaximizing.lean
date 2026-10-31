-- Prove2me | Definitions.Def_FastCore_IsWelfareMaximizing
-- name    : FastCore_IsWelfareMaximizing
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:01.687692+00:00
-- url     : https://prove2.me/theorems/25035c3e-39f2-4ba1-808a-6b83f2d66753
-- title:
--   Maximum welfare allocation
-- statement:
--   An allocation $\{x^*_i\}_{i\in N}$ is a **maximum welfare allocation** for the bids $\{b_i\}$ if it lies in the argmax of (1):
--
--   $$
--   \sum_{i\in N} b_i(x^*_i)\ \ge\ \sum_{i\in N} b_i(y_i)\qquad\text{for every allocation } y.
--   $$
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, eq. (1), p.11

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

open ComplementFreeCA.CFRounding (IsAllocation welfare)

namespace FastCore

/-- `x` is a welfare-maximizing allocation for the bids `b`: the argmax in (1) of Definition 1
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, eq. (1), p.11). -/
def IsWelfareMaximizing {n m : ℕ} (b : Bids n m) (x : Fin n → Finset (Fin m)) : Prop :=
  IsAllocation x ∧ ∀ y, IsAllocation y → welfare b y ≤ welfare b x

end FastCore


