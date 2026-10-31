-- Prove2me | Definitions.Def_FastCore_IsWinnerSet
-- name    : FastCore_IsWinnerSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:55.410405+00:00
-- url     : https://prove2.me/theorems/6de45af0-2cde-459b-92a5-b44007ff91d4
-- title:
--   Winner set (Definition 1, literal)
-- statement:
--   A subset $W\subseteq N$ is a **winner set** for the bids $\{b_i\}$ if $W=\{i\in N:x^*_i\neq\emptyset\}$ for some maximum welfare allocation $x^*$.
--
--   This is Definition 1 read literally: a bidder may be a winner with a bundle of value zero. The second bullet of Lemma 2 needs this reading. The zero-value convention of p.10 is `IsZeroFreeWinnerSet`.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11

import Mathlib
import Definitions.Def_FastCore_Bids
import Definitions.Def_FastCore_IsWelfareMaximizing
import Definitions.Def_FastCore_winners

namespace FastCore

/-- `W` is a winner set for the bids `b`, literally as in Definition 1
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11): `W = {i : x*ᵢ ≠ ∅}` for some welfare-maximizing allocation `x*`.
This reading allows a winner with a bundle of value zero; `IsZeroFreeWinnerSet` excludes that. -/
def IsWinnerSet {n m : ℕ} (b : Bids n m) (W : Finset (Fin n)) : Prop :=
  ∃ x, IsWelfareMaximizing b x ∧ W = winners x

end FastCore


