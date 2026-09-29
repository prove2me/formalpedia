-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_revenue
-- name    : OnlinePrimalDual_AdAuctions_revenue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:52:29.742075+00:00
-- url     : https://prove2.me/theorems/1665d161-97e3-4009-8860-7ddda1d131cd
-- title:
--   Buyer i's total accrued bid value (dual profit)
-- statement:
--   `revenue inst wonBids i := (wonBids i).sum`, the total bid value `∑_j b(i,j)y(i,j)` accrued
--   from buyer `i` over the run — the sum of the bids of the items actually allocated to `i`.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 213, used throughout the proof of Theorem 10.1, e.g. inequality (10.1)

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance

namespace OnlinePrimalDual.AdAuctions

/-- The total bid value `∑_j b(i,j)y(i,j)` accrued from buyer `i` over the run, i.e. the sum of
the bids of the items actually allocated to `i`, given as the list `wonBids i` in allocation
order — the book's own dual-profit quantity for buyer `i` (used throughout the proof of Theorem
10.1, e.g. inequality (10.1), p. 213). **`wonBids i` is precisely the items for which `i` was
actually charged**, not every item the argmax rule assigns to `i` (clarified per
`CHANGES_REQUESTED.md`'s non-blocking note, 2026-09-21 — see `buyerX`'s doc-comment for why the
distinction matters: step (2)'s "if `x(i) ≥ 1`, do nothing" means an assigned item need not be a
charged one). -/
noncomputable def revenue {I M : Type*} [Fintype I] [Fintype M]
    (_inst : AdAuctionsInstance I M) (wonBids : I → List ℝ) (i : I) : ℝ :=
  (wonBids i).sum

end OnlinePrimalDual.AdAuctions


