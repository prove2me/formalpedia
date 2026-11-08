-- Prove2me | Definitions.Def_TightClock_IsValidSingleStep
-- name    : TightClock_IsValidSingleStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:10:36.510207+00:00
-- url     : https://prove2.me/theorems/cc83880f-67ff-4e13-90c9-fc6c04b2064b
-- title:
--   Validity of a single-step clock
-- statement:
--   A single-step clock is **valid** for $\mathcal F$ if on every run from a nonnegative profile:
--
--   1. each test is of an active bidder with cutoff $j\ge1$;
--   2. whenever it stops with a set $S$, we have $S\in\mathcal F$ and every member of $S$ is active.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_TightClock_ssHist

set_option autoImplicit false

namespace TightClock

/-- A valid single-step clock, on every run from every nonnegative profile: "in each step it picks an active
bidder with some cutoff j ≥ 1"; and "The auction may stop at any time and serve any feasible set of active
bidders." Afshinmehr et al., manuscript (STOC 2027 submission), §6.2, p.35 (PDF 38). -/
def IsValidSingleStep (q L : ℕ) (F : Finset (Finset (Fin (bidderCount q L))))
    (σ : SingleStepStrategy (bidderCount q L)) : Prop :=
  ∀ v : Fin (bidderCount q L) → ℝ, (∀ i, 0 ≤ v i) → ∀ t : ℕ,
    match σ (ssHist q L σ v t) with
    | .test i => ∃ j : Fin (L + 1), stateOf q L (ssHist q L σ v t) i = some j ∧ 1 ≤ j.val
    | .stop S => S ∈ F ∧ ∀ i ∈ S, stateOf q L (ssHist q L σ v t) i ≠ none

end TightClock


