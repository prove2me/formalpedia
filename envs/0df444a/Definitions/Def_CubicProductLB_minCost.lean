-- Prove2me | Definitions.Def_CubicProductLB_minCost
-- name    : CubicProductLB_minCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:20:36.084135+00:00
-- url     : https://prove2.me/theorems/a9891f5f-c87e-45aa-9019-42bef0cc6b25
-- title:
--   The minimum occurrence cost $L_d(n)$
-- statement:
--   $L_d(n)$ is the minimum occurrence cost among product representations of $F_{p,n}$ with factors of degree at most $d$, and $L_d(n) = +\infty$ if there is no such representation.
--
--   **Formalization Note** The value lies in $\mathbb N \cup \{\infty\}$ (`ℕ∞`), where the infimum over an empty family is $\infty$, which is the page's convention.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (369), p.42

import Mathlib
import Definitions.Def_CubicProductLB_ProductRep

namespace CubicProductLB

/-- `L_d(n)`: the minimum occurrence cost among degree-`d` representations of `F_{p,n}`, and
`+∞` if the class is empty (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Eq. (369), p.42).

**Formalization Note** In `ℕ∞` the infimum over an empty family is `⊤`, which is the page's `+∞`. -/
noncomputable def minCost (d p n : ℕ) : ℕ∞ :=
  ⨅ r : ProductRep d p n, (r.cost : ℕ∞)

end CubicProductLB


