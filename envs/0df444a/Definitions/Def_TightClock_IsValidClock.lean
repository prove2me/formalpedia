-- Prove2me | Definitions.Def_TightClock_IsValidClock
-- name    : TightClock_IsValidClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:58:56.712204+00:00
-- url     : https://prove2.me/theorems/52090514-2073-4b8c-ba28-e4c820e76d74
-- title:
--   The rules of a valid clock auction
-- statement:
--   A deterministic clock is **valid** for $\mathcal F$ if on every run from a nonnegative profile:
--
--   1. it offers prices only to active bidders;
--   2. each price offered to $i$ is nonnegative and at least every earlier offer to $i$;
--   3. whenever it stops with a set $S$, we have $S\in\mathcal F$ and every member of $S$ is active.
--
--   This is the clock of §3 with the relaxations of §6.1: the auction may continue after its active set has become feasible, and may serve any feasible subset of its active bidders. Since the rejecting bidders are the only ones who leave, a bidder cannot be reinstated after rejection.
--
--   **Formalization Note** Every bidder starts active at price $0$, so the first offer is at least $0$. Asking for the rules on all nonnegative profiles loses nothing, because a clock may stop with $\emptyset$ at histories that the prior cannot produce.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16); §6.1, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_TightClock_clockHist
import Definitions.Def_TightClock_IsActive

set_option autoImplicit false

namespace TightClock

/-- The rules of §3 with the relaxations of §6.1, on every run from every nonnegative profile: offers go
only to active bidders; each price is nonnegative and at least every earlier offer to that bidder; every
`stop S` has `S ∈ F` and `S` inside the active set. Afshinmehr et al., manuscript (STOC 2027 submission),
§3, p.13 (PDF 16); §6.1, p.34 (PDF 37): auctions "may continue to make offers after their active set has
become feasible, and may serve any feasible subset of their active bidders."

**Formalization Note** A bidder starts "active at price 0", so the first offer is at least `0`. Requiring
the rules on all nonnegative profiles loses nothing: a clock can stop with `∅` at histories that the prior
cannot produce. -/
def IsValidClock {n : ℕ} (F : Finset (Finset (Fin n))) (σ : Strategy n) : Prop :=
  ∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i) → ∀ t : ℕ,
    match σ (clockHist σ v t) with
    | .offer i p =>
        IsActive (clockHist σ v t) i ∧ 0 ≤ p ∧
          ∀ e ∈ clockHist σ v t, e.bidder = i → e.price ≤ p
    | .stop S => S ∈ F ∧ ∀ i ∈ S, IsActive (clockHist σ v t) i

end TightClock


