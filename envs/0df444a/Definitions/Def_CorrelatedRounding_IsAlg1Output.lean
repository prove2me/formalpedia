-- Prove2me | Definitions.Def_CorrelatedRounding_IsAlg1Output
-- name    : CorrelatedRounding_IsAlg1Output
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:07.003205+00:00
-- url     : https://prove2.me/theorems/bdc9fa49-83f5-4004-8ac6-abe09fc09ca4
-- title:
--   Output of Algorithm 1 for a realization of the clocks
-- statement:
--   A map $z$ from items to FCs is an output of Algorithm 1 for the realization $E$ when, for every item $i$,
--   $$z(i)\in\arg\min_{k}\ \frac{y_k}{u_{ki}}E_k .$$
--   Any element of the arg min qualifies, so this covers every way of breaking ties.
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Algorithm 1, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_clock

namespace CorrelatedRounding

/-- **Output of Algorithm 1 for a realization of the clocks.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4,
Algorithm 1, p.10: "Z_i ← arg min_{k=1,…,K} (y_k/u_ki) E_k ⊲ Break ties arbitrarily".

`IsAlg1Output u E z` says that for every item `i`, the FC `z i` attains the minimum of the clocks of `i`.

**Formalization Note.** Any element of the arg min qualifies, which is the reading of "break ties
arbitrarily" (no fixed rule). -/
def IsAlg1Output {q K : ℕ} (u : Fin K → Fin q → ℝ) (E : Fin K → ℝ) (z : Fin q → Fin K) : Prop :=
  ∀ i k', clock u E (z i) i ≤ clock u E k' i

end CorrelatedRounding


