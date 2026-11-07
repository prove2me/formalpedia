-- Prove2me | Definitions.Def_BorderD4_sumProduct
-- name    : BorderD4_sumProduct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:58:14.750506+00:00
-- url     : https://prove2.me/theorems/4ff0cca0-f034-4cd2-b2b1-6ab5cc94309f
-- title:
--   The sum-product polynomial $P_{k+1,n}$
-- statement:
--   For $k\ge 0$ and $n\ge 1$, the sum-product polynomial is
--   $$P_{k+1,n}=\sum_{j=1}^{k+1}\prod_{t=(j-1)n+1}^{jn}x_t,$$
--   the sum of $k+1$ monomials of degree $n$ on disjoint blocks of variables, in $N=(k+1)n$ variables. It is the hard polynomial of the mission.
--
--   **Formalization Note** The variables are indexed by pairs $(j,t)$ in $\mathrm{Fin}(k+1)\times\mathrm{Fin}\,n$, which is the page's polynomial up to renaming.
-- source:
--   A. Dey, P. Dutta, Z. Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 1.2, p.4

import Mathlib
set_option autoImplicit false

open MvPolynomial
open scoped PowerSeries

namespace BorderD4

/-- The sum-product polynomial `P_{k+1,n} = ∑_{j=1}^{k+1} ∏_{t=(j−1)n+1}^{jn} x_t`.
Source: Dey, Dutta, Guo, An Exponential Top Fan-In Hierarchy for Border Depth-4 Circuits, STOC 2027 submission (manuscript sha256 518aaf99…), Definition 1.2, p.4.

**Formalization Note** The `N = (k+1)n` variables are indexed by `Fin (k+1) × Fin n`: the pair `(j, t)`
is the `t`-th variable of block `j`. This is the page's polynomial up to renaming the variables. -/
noncomputable def sumProduct (F : Type*) [Field F] (k n : ℕ) : MvPolynomial (Fin (k + 1) × Fin n) F :=
  ∑ j : Fin (k + 1), ∏ t : Fin n, X (j, t)

end BorderD4


