-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_SelfBounding
-- name    : AdaptiveRLDC_LowerBound_SelfBounding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:16.549191+00:00
-- url     : https://prove2.me/theorems/d2ba2d26-1fdd-407a-89f3-ff9ac604800f
-- title:
--   Strong self-bounding with coordinate-deleted witnesses
-- statement:
--   For $a,b\ge0$, a nonnegative function $f$ on a binary cube is strongly $(a,b)$-self-bounding if nonnegative coordinate-deleted functions $g_i$ exist such that, for every $x$,
--   $$0\le f(x)-g_i(x^{(i)})\le1,\qquad\sum_i(f(x)-g_i(x^{(i)}))\le af(x)+b.$$
--   Each $g_i$ has as domain precisely the coordinates other than $i$. No monotonicity condition or fixed witness is imposed. This is the general source predicate needed for the entire parameter ranges of the two tail theorems.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), Definition 4.7, printed p.18, PDF p.19; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Definition 4.7: fully existential nonnegative coordinate-deleted witnesses. -/
def StronglySelfBounding {n : ℕ} (f : Cube n → ℝ) (a b : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ (∀ x, 0 ≤ f x) ∧
  ∃ g : (i : Fin n) → ({j : Fin n // j ≠ i} → Bool) → ℝ,
    (∀ i z, 0 ≤ g i z) ∧
    (∀ i x, 0 ≤ f x - g i (fun j => x j.val) ∧
      f x - g i (fun j => x j.val) ≤ 1) ∧
    ∀ x, (∑ i, (f x - g i (fun j => x j.val))) ≤ a * f x + b

end AdaptiveRLDC.LowerBound


