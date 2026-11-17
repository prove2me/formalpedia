-- Prove2me | Definitions.Def_FixpReciprocal_Supplement_Classes
-- name    : FixpReciprocal_Supplement_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:49:03.937652+00:00
-- url     : https://prove2.me/theorems/56e52a85-693b-43ac-aa81-e33d81752647
-- title:
--   Instance classes of Theorems 5.2, 6.2 and 7.2
-- statement:
--   This item fixes the instance classes of the paper's three auction theorems, on top of the published market models.
--
--   1. **ROI pacing (Theorem 5.2).** A pacing market with $n$ bidders, $m$ items and nonnegative rational values $v_{\ell,s}$ belongs to the class when $n\ge 2$, $m\ge 1$, and every item has a positive value to at least one bidder: $\max_{\ell\in[n]}v_{\ell,s}>0$ for every $s\in[m]$.
--   2. **GSP autobidding (Theorem 6.2).** A GSP sponsored-shopping auction belongs to the class when there is one advertising slot per item ($K=|\mathcal J|$, the number of items) and every click-through rate equals $1$.
--   3. **Throttling, fixed priority (Theorem 7.2).** Ties between equal bids are broken by a fixed priority order, here the bidder index order: bidder $0$ has the highest priority, then bidder $1$, and so on.
--   4. **Throttling, sparse class (Theorem 7.2, hardness clause).** Every item has at most three positive bids, and the positive bids on the same item are pairwise distinct.
--
--   Restricting the published search problems to these classes gives exactly the problems stated in Theorems 5.2, 6.2 and 7.2.
--
--   **Formalization Note** Each class is a predicate passed as the restriction argument of the published `roiPacingProblemOn`, `budgetGSPProblemOn` and `throttlingProblemOn`. The input of Theorem 7.2 is only the bids and budgets, so the priority is fixed rather than given; any fixed order becomes the index order after relabelling the bidders.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), §5.1, p.16 (PDF p.18) and Theorem 5.2, p.17 (PDF p.19); §6.1, p.21 (PDF p.23) and Theorem 6.2, p.22 (PDF p.24); §7.1, p.30 (PDF p.32) and Theorem 7.2, p.31 (PDF p.33)

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_ROIPacing
import Definitions.Def_ExactAutobid_Equilibria_GSP
import Definitions.Def_ExactAutobid_Equilibria_Throttling

namespace FixpReciprocal.Supplement

open ExactAutobid.Equilibria AutobiddingGSP.Approximation

/-- **The instances of Theorem 5.2**: `n ≥ 2` bidders, `m ≥ 1` items, and every item has a positive
value to at least one bidder (`max_ℓ v_{ℓ,s} > 0` for every `s`).

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), §5.1, p.16 and Theorem 5.2, p.17.

**Formalization Note.** Used as the restriction `R` of the published
`ExactAutobid.Equilibria.roiPacingProblemOn`, whose `WellFormed` already gives `n` rows of `m`
nonnegative rational values. -/
def ShimizuPacing (d : PacingData) : Prop :=
  2 ≤ d.nb ∧ 1 ≤ d.ng ∧ ∀ j : Fin d.ng, ∃ i : Fin d.nb, 0 < d.val i j

/-- **The instances of Theorem 6.2**: one advertising slot per item (`K = M`, the total number of
items) and click-through rate one at every slot.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), §6.1, p.21 and Theorem 6.2, p.22.

**Formalization Note.** Used as the restriction `R` of the published
`ExactAutobid.Equilibria.budgetGSPProblemOn`. No bound on the number of items per bidder is
imposed. -/
def OneSlotUnitCTR (Au : Auction) : Prop :=
  Au.K = Au.vals.flatten.length ∧ ∀ q ∈ Au.ctr, q = 1

/-- **The fixed tie-breaking priority of Theorem 7.2**: bidders in index order, a lower index
having higher priority (`prio = [0, 1, …, n − 1]`).

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), §7.1, p.30 ("Ties are resolved by a fixed priority order").

**Formalization Note.** The input of Theorem 7.2 is only the bids and the budgets, so the priority is
not instance data: it is fixed to the index order (any fixed order is this one after relabelling the
bidders). -/
def IndexPriority (d : ThrottleData) : Prop :=
  d.prio = List.range d.nb

/-- **The sparse class of Theorem 7.2's hardness clause**: each item has at most three positive bids,
and the positive bids on the same item are pairwise distinct.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027
submission (sha256 ffcad4a7…), Theorem 7.2, p.31. -/
def ThreeDistinctBids (d : ThrottleData) : Prop :=
  ∀ j : Fin d.ng, (Finset.univ.filter (fun i : Fin d.nb => 0 < d.bid i j)).card ≤ 3 ∧
    ∀ i k : Fin d.nb, 0 < d.bid i j → 0 < d.bid k j → d.bid i j = d.bid k j → i = k

end FixpReciprocal.Supplement


