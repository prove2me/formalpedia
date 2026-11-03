-- Prove2me | Definitions.Def_WeightedCongestionBR_phiPoly
-- name    : WeightedCongestionBR_phiPoly
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:15:48.329561+00:00
-- url     : https://prove2.me/theorems/f6544e99-0722-4fb9-bc44-3071beeb7087
-- title:
--   Faulhaber potential $\phi_e$, (5)
-- statement:
--   For a polynomial $c(x)=\sum_{\nu=0}^d a_\nu x^\nu$,
--
--   $$
--   \phi(x)=a_0\,x+\sum_{\nu=1}^d a_\nu\Big(x^{\nu+1}+\frac{\nu+1}{2}x^\nu\Big).
--   $$
--
--   Applied to the cost of a resource it gives the paper's resource potential $\phi_e$, a variant of the Faulhaber potential of Christodoulou et al.; summed over resources it is an $\alpha$-approximate potential of the game (Lemmas 4–6).
--
--   **Formalization Note** The sum runs to the degree of the polynomial, which is the paper's sum to $d$ since higher coefficients vanish.
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, eq. (5), p.11

import Mathlib
set_option autoImplicit false
open scoped NNReal

namespace WeightedCongestionBR

/-- The **Faulhaber-type potential** of a resource (Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, eq. (5), p.11): for
`c(x) = ∑_{ν=0}^d a_ν x^ν`,
`φ(x) := a_0 x + ∑_{ν=1}^d a_ν (x^{ν+1} + ((ν+1)/2) x^ν)`.

**Formalization Note** The polynomial is passed as `P`; the sum runs over `1 ≤ ν ≤ natDegree P`,
which equals the paper's sum to `d` because the coefficients above the degree vanish. -/
noncomputable def phiPoly (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  P.coeff 0 * x +
    ∑ ν ∈ Finset.Icc 1 P.natDegree, P.coeff ν * (x ^ (ν + 1) + ((ν : ℝ) + 1) / 2 * x ^ ν)

end WeightedCongestionBR


