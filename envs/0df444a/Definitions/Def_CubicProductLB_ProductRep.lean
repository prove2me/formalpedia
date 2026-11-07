-- Prove2me | Definitions.Def_CubicProductLB_ProductRep
-- name    : CubicProductLB_ProductRep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:17:29.694118+00:00
-- url     : https://prove2.me/theorems/d2e6ff09-f701-4b92-a94a-b1f72da87889
-- title:
--   Product representations of $F_{p,n}$ and their occurrence cost
-- statement:
--   A **product representation** of $F_{p,n}$ with factors of degree at most $d$ is a finite list of listed factors $P_1, \dots, P_m$, each of multilinear degree at most $d$ on $X_n$, such that
--   $$\prod_{j=1}^m P_j(x) = F_{p,n}(x) \quad \text{for every } x \in X_n.$$
--   Its **occurrence cost** $C$ is the sum of the factor costs. The definition also names its positive-cost factors, in order, and their number $S$; these are the objects of Step 3 of the proof of Theorem 5.
--
--   **Formalization Note** Equality is pointwise on $X_n$, not an identity of formal polynomials, and the number of factors is unrestricted.
-- source:
--   Fu–Fu, Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1, p.3; Definition 2, p.4; Eq. (369), p.42; Eq. (344), p.39

import Mathlib
import Definitions.Def_CubicProductLB_signCube
import Definitions.Def_CubicProductLB_signedMod
import Definitions.Def_CubicProductLB_ListedFactor
import Definitions.Def_CubicProductLB_HasMultilinearDegLE

namespace CubicProductLB

/-- A product representation of `F_{p,n}` with factors of multilinear degree at most `d` on `X_n`:
a finite list of listed factors whose product agrees with `F_{p,n}` at every point of `X_n`
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 1, p.3 for `d = 3`; Eq. (369), p.42 for general `d`).

**Formalization Note** Equality is pointwise on `X_n`, not of formal polynomials. -/
structure ProductRep (d p n : ℕ) where
  /-- the listed factors `P_1, …, P_m` -/
  factors : List (ListedFactor n)
  /-- every factor has multilinear degree at most `d` on `X_n` -/
  deg_le : ∀ l ∈ factors, HasMultilinearDegLE d (ListedFactor.eval l)
  /-- the product agrees with `F_{p,n}` on `X_n` -/
  rep : ∀ x ∈ signCube n, (factors.map fun l => ListedFactor.eval l x).prod = signedMod p n x

/-- The occurrence cost `C` of a product: the sum of the factor costs
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), Definition 2, p.4). -/
def ProductRep.cost {d p n : ℕ} (r : ProductRep d p n) : ℕ :=
  (r.factors.map ListedFactor.cost).sum

/-- The positive-cost factors of a product, in order
(Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Step 3, p.39). -/
def ProductRep.posFactors {d p n : ℕ} (r : ProductRep d p n) : List (ListedFactor n) :=
  r.factors.filter fun l => decide (0 < ListedFactor.cost l)

/-- The number `S` of positive-cost factors (Fu–Fu, *Exponential Lower Bounds for Products of Cubic Polynomials over Prime Fields*, arXiv:2611.02385 (held version sha256 183edf14…), proof of Theorem 5, Eq. (344), p.39). -/
def ProductRep.posCount {d p n : ℕ} (r : ProductRep d p n) : ℕ :=
  r.posFactors.length

end CubicProductLB


