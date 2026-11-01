-- Prove2me | Definitions.Def_RedundancyHT_cocWeight
-- name    : RedundancyHT_cocWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:25:50.0248+00:00
-- url     : https://prove2.me/theorems/6d53fc68-c7b9-4d3f-bf49-70d6a489c803
-- title:
--   The product-form weight $\prod_i N\lambda p_{c_i}/\mu(c_1,\dots,c_i)$ of (3)
-- statement:
--   For a sequence $c=(c_1,\dots,c_M)$ of job types,
--   $$\prod_{i=1}^{M}\frac{N\lambda p_{c_i}}{\mu(c_1,\dots,c_i)},\qquad \mu(c_1,\dots,c_i)=\sum_{n\in\bigcup_{m=1}^{i}c_m}\mu_n.$$
--   The empty sequence has weight one.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, displays (3), (4), p.7

import Definitions.Def_RedundancyHT_muSet
import Definitions.Def_RedundancyHT_pOf

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The product of (3)**: `∏_{i=1}^{M} N λ p_{c_i} / µ(c₁,…,c_i)` for `c = (c₁,…,c_M)`
(arXiv:2005.14566v5, p.7). The prefix rate of (4) is `muSet` of the set of the first `i` entries. -/
def cocWeight {n m : ℕ} (D : Model n m) (lam : ℝ) (c : List (Fin n)) : ℝ :=
  ∏ i : Fin c.length,
    (m : ℝ) * lam * pOf D (c.get i) / muSet D (c.take (i.val + 1)).toFinset

end RedundancyHT


