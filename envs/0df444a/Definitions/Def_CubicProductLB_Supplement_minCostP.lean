-- Prove2me | Definitions.Def_CubicProductLB_Supplement_minCostP
-- name    : CubicProductLB_Supplement_minCostP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:39:07.98094+00:00
-- url     : https://prove2.me/theorems/43a29851-96f6-46f1-8e0b-461b7a362708
-- title:
--   $L^{(p,q)}_d(n)$: minimum occurrence cost over $\mathbb F_p$
-- statement:
--   $L^{(p,q)}_d(n)$ is the minimum total variable-occurrence cost of an exact degree-$d$ product representation of $F_{q,n}$ over $\mathbb F_p$, and $+\infty$ when no representation exists:
--   $$L^{(p,q)}_d(n) = \inf\{\mathrm{cost}(P_1,\dots,P_m) : F_{q,n} = \textstyle\prod_j P_j \text{ on } \{-1,1\}^n,\ \deg P_j \le d\}.$$
--
--   **Formalization Note** Valued in $\mathbb N \cup \{\infty\}$, where the infimum of the empty family is $\infty$ (the convention stated after Eq. (369)).
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.14, p.65; Eq. (369), p.42

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_ProductRepP

namespace CubicProductLB.Supplement

/-- `L^{(p,q)}_d(n)`: the minimum total variable-occurrence cost of an exact degree-`d` representation
of `F_{q,n}` over `F_p`, and `+∞` if there is none (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.14, p.65).

**Formalization Note** In `ℕ∞` the infimum over an empty family is `⊤`, the convention of Eq. (369),
p.42. -/
noncomputable def minCostP (d p q n : ℕ) : ℕ∞ :=
  ⨅ r : ProductRepP d p q n, (r.cost : ℕ∞)

end CubicProductLB.Supplement


