-- Prove2me | Definitions.Def_TightClock_Supplement_retainOnly
-- name    : TightClock_Supplement_retainOnly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T18:07:28.353073+00:00
-- url     : https://prove2.me/theorems/7410bafa-a14b-428d-9bec-6b909a2b4b89
-- title:
--   $\mathrm{RetainOnly}(S)$
-- statement:
--   $\mathrm{RetainOnly}(S)$ freezes the active bidders in $S$ and raises the price of every other active bidder by successive grid offers until she exits, without using the values these exits reveal. The auction then terminates and serves its active set, which is now contained in $S$.
--
--   **Formalization Note** The bidders outside $S$ are raised one at a time in index order; the outcome does not depend on the order.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, pp.13–14 (PDF pp.16–17)

import Mathlib
import Definitions.Def_TightClock_Supplement_offerTo
import Definitions.Def_TightClock_Supplement_nextGrid

set_option autoImplicit false

namespace TightClock.Supplement

/-- `RetainOnly(S)` followed by termination: freeze the active bidders of `S` and raise every other
active bidder by successive grid offers until she exits; then return the active set (now inside `S`),
which the auction serves. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, pp.13–14 (PDF 16–17): "RetainOnly(S) freezes the active
bidders in S and raises the prices of all other active bidders until they exit, without using the
values revealed by those exits."

**Formalization Note** The bidders outside `S` are raised one at a time, the least index first; the
order does not affect the outcome. -/
noncomputable def retainOnly {n : ℕ} (δ : ℝ) (st0 : CState n) (S : Finset (Fin n)) :
    ClockProg n (Finset (Fin n)) :=
  ClockProg.loop (fun st : CState n =>
    match (List.finRange n).find? (fun i => decide (i ∈ st.active ∧ i ∉ S)) with
    | none => ClockProg.pure (Sum.inr st.active)
    | some i => do
        let (_, st') ← offerTo st i (nextGrid δ (st.price i))
        return Sum.inl st') st0

end TightClock.Supplement


