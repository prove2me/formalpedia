-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_actualCharge
-- name    : OnlinePrimalDual_AdAuctions_actualCharge
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:53:13.689732+00:00
-- url     : https://prove2.me/theorems/fdc28aed-ddba-47b9-8ce6-34faa0804835
-- title:
--   Buyer i's actual charged revenue
-- statement:
--   `actualCharge inst wonBids i := min (revenue inst wonBids i) (B i)`, the minimum between the
--   sum of the bids of the items allocated to buyer `i` and buyer `i`'s total budget — the book's
--   own definition of the revenue actually collected.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 211

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_revenue

namespace OnlinePrimalDual.AdAuctions

/-- The actual revenue collected from buyer `i`: "the minimum between the sum of the bids of the
items allocated to a buyer... and the total budget of the buyer. That is, buyers can never be
charged by more than their total budget." (p. 211). -/
noncomputable def actualCharge {I M : Type*} [Fintype I] [Fintype M]
    (inst : AdAuctionsInstance I M) (wonBids : I → List ℝ) (i : I) : ℝ :=
  min (revenue inst wonBids i) (inst.B i)

end OnlinePrimalDual.AdAuctions


