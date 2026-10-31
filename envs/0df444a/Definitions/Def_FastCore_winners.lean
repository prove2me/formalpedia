-- Prove2me | Definitions.Def_FastCore_winners
-- name    : FastCore_winners
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:22.930462+00:00
-- url     : https://prove2.me/theorems/87baef90-ea3a-4112-9352-50a6658be3ad
-- title:
--   The winners of an allocation
-- statement:
--   The **winners** of an allocation $x$ are the bidders who receive a nonempty bundle: $\{i\in N: x_i\ne\emptyset\}$.
-- source:
--   Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11

import Mathlib

namespace FastCore

/-- The bidders who receive a nonempty bundle: `{i ∈ N : xᵢ ≠ ∅}`
(Niazadeh et al., Fast Core Pricing for Rich Advertising Auctions, arXiv:1610.03564v4, Definition 1, p.11). -/
def winners {n m : ℕ} (x : Fin n → Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ ∅)

end FastCore


