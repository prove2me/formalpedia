-- Prove2me | Definitions.Def_TightClock_Supplement_IsStrictClock
-- name    : TightClock_Supplement_IsStrictClock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T17:59:45.983439+00:00
-- url     : https://prove2.me/theorems/2f11c7a6-7c58-45a9-bb2c-c39e9fda9bea
-- title:
--   Clock auction for $\mathcal F$ under the strict rules of §3
-- statement:
--   A deterministic clock auction $\sigma$ is a **clock auction for** $\mathcal F$ under the rules of §3 if, on every run from every nonnegative value profile:
--
--   1. it offers prices only to active bidders, every price is nonnegative and at least every earlier offer to that bidder, and whenever it stops with a set $S$, $S\in\mathcal F$ and every member of $S$ is active (the published validity predicate);
--   2. when it stops, it serves **all** of its active bidders: every bidder who is still active belongs to $S$;
--   3. it terminates.
--
--   Clause 2 is the §3 rule that "the auction terminates with a feasible set of active bidders, all of whom are served", so an active bidder who is not served must be removed by a price she rejects. The published `TightClock.IsValidClock` is the relaxed class of §6.1 used for the lower bound; the upper bounds of §4 and §5 claim the strict rule.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.13 (PDF p.16)

import Mathlib
import Definitions.Def_TightClock_IsValidClock
import Definitions.Def_TightClock_StopsWith

set_option autoImplicit false

namespace TightClock.Supplement

/-- A deterministic clock auction for `F` under the strict rules of §3: it obeys the rules of
`TightClock.IsValidClock` (offers only to active bidders, nondecreasing nonnegative prices, every
`stop S` has `S ∈ F` and `S` active), it **serves its whole active set** when it stops, and it
terminates on every nonnegative profile. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027 submission), §3, p.13 (PDF 16): "The auction terminates with a
feasible set of active bidders, all of whom are served. In particular, an active bidder who is not
intended to be served must be removed through an actual price increase that she rejects."

**Formalization Note** `TightClock.IsValidClock` is the relaxed class of §6.1 (any feasible subset of
the active set may be served); the second clause restores the §3 rule. The third clause is the
termination of the §3 auction ("The auction terminates ..."). -/
def IsStrictClock {n : ℕ} (F : Finset (Finset (Fin n))) (σ : Strategy n) : Prop :=
  IsValidClock F σ ∧
  (∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i) → ∀ (t : ℕ) (S : Finset (Fin n)),
    σ (clockHist σ v t) = .stop S → ∀ i, IsActive (clockHist σ v t) i → i ∈ S) ∧
  (∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i) → ∃ S, StopsWith σ v S)

end TightClock.Supplement


