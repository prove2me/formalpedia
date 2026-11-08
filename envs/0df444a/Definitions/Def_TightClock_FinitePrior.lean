-- Prove2me | Definitions.Def_TightClock_FinitePrior
-- name    : TightClock_FinitePrior
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:38:27.096188+00:00
-- url     : https://prove2.me/theorems/3c45acc0-0d56-4270-b836-f6034bc262d6
-- title:
--   Finitely supported law of one bidder's value
-- statement:
--   A **finite prior** is a probability law on finitely many nonnegative reals: a finite support, positive weights on it, and total weight $1$. In the i.i.d. prior of Theorem 6.1, the values $X_1,\dots,X_n$ are independent draws from one such law.
--
--   **Formalization Note** The same structure is the marginal of every bidder, so the prior is i.i.d. by construction. The weight function is read only on the support.
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §3, p.14 (PDF p.17); §6.1, p.34 (PDF p.37)

import Mathlib

set_option autoImplicit false

namespace TightClock

/-- A probability law on finitely many nonnegative points, the common law of every bidder in the
i.i.d. prior of Theorem 6.1. Afshinmehr et al., manuscript (STOC 2027 submission), §3, p.14 (PDF 17);
§6.1, p.34 (PDF 37).

**Formalization Note** One `FinitePrior` is the marginal of all bidders, so the prior is i.i.d. by
construction. The field `weight` is only read on `support`. -/
structure FinitePrior where
  /-- The finitely many values the law can take. -/
  support : Finset ℝ
  /-- The probability of each support point. -/
  weight : ℝ → ℝ
  /-- Values are nonnegative. -/
  nonneg : ∀ x ∈ support, 0 ≤ x
  /-- Every support point has positive probability. -/
  weight_pos : ∀ x ∈ support, 0 < weight x
  /-- The probabilities sum to one. -/
  weight_sum : ∑ x ∈ support, weight x = 1

end TightClock


