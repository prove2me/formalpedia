-- Prove2me | Definitions.Def_CubicProductLB_Supplement_ProductRepP
-- name    : CubicProductLB_Supplement_ProductRepP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:38:28.900554+00:00
-- url     : https://prove2.me/theorems/d35b7644-a050-41d9-8be0-acd1d6f88549
-- title:
--   Degree-$d$ product representation of $F_{q,n}$ over $\mathbb F_p$, and its cost
-- statement:
--   A **degree-$d$ product representation** of $F_{q,n}$ over $\mathbb F_p$ is a finite list of listed factors, each computing a function of multilinear degree at most $d$ on $\{-1,1\}^n$, whose product equals $F_{q,n}$ at every point of the sign cube:
--   $$F_{q,n}(x) = \prod_j P_j(x) \qquad (x \in \{-1,1\}^n).$$
--   Its **cost** is the total variable-occurrence cost, the sum of the costs of its listed factors.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.14, p.65; Eq. (369), p.42

import Mathlib
import Definitions.Def_CubicProductLB_Supplement_signCubeP
import Definitions.Def_CubicProductLB_Supplement_signedModP
import Definitions.Def_CubicProductLB_Supplement_ListedFactorP
import Definitions.Def_CubicProductLB_Supplement_HasMultilinearDegLEP

namespace CubicProductLB.Supplement

/-- An exact representation of `F_{q,n}` over `F_p` by a product of listed factors of degree at most
`d` on the sign cube (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Section 15.14, p.65, the display defining `L^{(p,q)}_d(n)`).

**Formalization Note** Equality is pointwise on `{-1, 1}^n`. The degree of a factor is the
multilinear degree of the function it computes on the cube, as in the base mission's
`CubicProductLB.ProductRep`. -/
structure ProductRepP (d p q n : ℕ) where
  /-- the listed factors -/
  factors : List (ListedFactorP p n)
  /-- every factor has multilinear degree at most `d` on the sign cube -/
  deg_le : ∀ l ∈ factors, HasMultilinearDegLEP d (ListedFactorP.eval l)
  /-- the product agrees with `F_{q,n}` on the sign cube -/
  rep : ∀ x ∈ signCubeP p n,
    (factors.map fun l => ListedFactorP.eval l x).prod = signedModP p q n x

/-- The total variable-occurrence cost of a representation: the sum of its factor costs. -/
def ProductRepP.cost {d p q n : ℕ} (r : ProductRepP d p q n) : ℕ :=
  (r.factors.map ListedFactorP.cost).sum

end CubicProductLB.Supplement


