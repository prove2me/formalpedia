-- Prove2me | Definitions.Def_OnlinePrimalDual_AdAuctions_allocRun_v2
-- name    : OnlinePrimalDual_AdAuctions_allocRun_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:17:13.370897+00:00
-- url     : https://prove2.me/theorems/dbbfd762-f01c-4656-8784-c4f47d4e7b16
-- title:
--   The Allocation algorithm's run: charged-bid lists computed from the arrival order and the argmax choice
-- statement:
--   `allocRun inst ord alloc` processes the items in the order `ord`; item $j$ goes to buyer $i = \texttt{alloc}\, j$ (the theorem requires `alloc` to realize the argmax rule $\arg\max_i b(i,j)(1-x(i))$); if $x(i) \ge 1$ already (with $x(i) = \texttt{buyerX}$ of $i$'s current list, step (3)'s update) nothing happens, otherwise $b(i,j)$ is appended to $i$'s list of charged bids, which updates $x(i)$. The output is the family of charged-bid lists, from which `revenue`, `actualCharge` and `buyerX` are computed.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 212, the Allocation algorithm

import Mathlib
import Definitions.Def_OnlinePrimalDual_AdAuctions_AdAuctionsInstance
import Definitions.Def_OnlinePrimalDual_AdAuctions_cParam
import Definitions.Def_OnlinePrimalDual_AdAuctions_buyerX

namespace OnlinePrimalDual.AdAuctions

/-- The run of the Allocation algorithm of Buchbinder & Naor, *The Design of Competitive Online
Algorithms via a Primal-Dual Approach*, FnT TCS 2009, Section 10.1 (p. 212), on the instance
`inst`, the items arriving in the order `ord : List M` and the algorithm's argmax choice being
`alloc : M → I` (the buyer `i` maximizing `b(i,j)(1 − x(i))` at the moment item `j` arrives —
a property of `alloc` the theorems state as a hypothesis, since the book leaves ties arbitrary).
The output is, for each buyer `i`, the list `wonBids i` of the bids of the items for which `i`
was actually charged, in allocation order: when item `j` arrives it is allocated to
`i = alloc j`; if `x(i) ≥ 1` already (`x(i) = buyerX inst i (wonBids i)`, the primal value
maintained by step (3)'s update, which `buyerX` realizes) the algorithm does nothing; otherwise
`i` is charged for `j` (the minimum of `b(i,j)` and its remaining budget — the total charge is
`actualCharge`) and `b(i,j)` is appended to `wonBids i`, which updates `x(i)` by step (3),
`x(i) ← x(i)(1 + b(i,j)/B(i)) + b(i,j)/((c−1)B(i))`. -/
noncomputable def allocRun {I M : Type*} [Fintype I] [Fintype M] [DecidableEq I]
    (inst : AdAuctionsInstance I M) (ord : List M) (alloc : M → I) : I → List ℝ :=
  ord.foldl
    (fun won j =>
      if 1 ≤ buyerX inst (alloc j) (won (alloc j)) then won
      else Function.update won (alloc j) (won (alloc j) ++ [inst.b (alloc j) j]))
    (fun _ => [])

end OnlinePrimalDual.AdAuctions


