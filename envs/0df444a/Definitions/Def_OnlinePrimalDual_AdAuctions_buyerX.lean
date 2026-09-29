-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX
-- name    : OnlinePrimalDual_AdAuctions_buyerX
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:51:59.302514+00:00
-- url     : https://prove2.me/theorems/ef23f852-a82d-43db-b2ec-818c3afbf599
-- title:
--   Buyer i's final primal value, as a fold over the bids won
-- statement:
--   Given the (temporally ordered) list `bids` of bid values for items actually allocated to
--   buyer `i`, `buyerX` realizes step (3)'s update `x(i) ← x(i)(1+bd/B(i)) + bd/((c-1)B(i))`,
--   applied once per allocation to `i` in order, starting from `x(i)=0`, as a left fold.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 212, Allocation algorithm, step (3)

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam

namespace OnlinePrimalDual.AdAuctions

/-- Buyer `i`'s final primal value `x(i)`, given the (temporally ordered) list `bids` of bid
values for the items actually allocated to buyer `i` during the run. **`bids` (`wonBids i` at the
call site) is precisely the items for which `i` was actually charged and `x(i)` actually updated**
(clarified per `CHANGES_REQUESTED.md`'s non-blocking note, 2026-09-21) — not every item the
algorithm's argmax rule assigns to `i`: the algorithm's own step (2), "if `x(i) ≥ 1`, do nothing"
(p. 212), means an item can be assigned to the argmax buyer `i` without that allocation ever
charging `i` or touching `x(i)`, and such items are excluded from this list. The Allocation
algorithm's step (3) (p. 212) updates, each time an item with bid `bd` is allocated to `i` *and
charged* (i.e. is in `bids`): `x(i) ← x(i)(1 + bd/B(i)) + bd/((c−1)B(i))` — an affine map in `x(i)`
depending on `bd`, applied once per charged allocation to `i`, starting from `x(i) = 0`
("Initially, for each buyer `i`, `x(i) ← 0`", p. 212). `buyerX` realizes this exactly as a left
fold over `bids` in allocation order. -/
noncomputable def buyerX {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (i : I) (bids : List ℝ) : ℝ :=
  bids.foldl (fun x bd => x * (1 + bd / inst.B i) + bd / ((cParam inst - 1) * inst.B i)) 0

end OnlinePrimalDual.AdAuctions


