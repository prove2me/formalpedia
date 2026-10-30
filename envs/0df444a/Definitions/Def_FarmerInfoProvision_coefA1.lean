-- Prove2me | Definitions.Def_FarmerInfoProvision_coefA1
-- name    : FarmerInfoProvision_coefA1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:24.375366+00:00
-- url     : https://prove2.me/theorems/e3b09c37-98c1-44f3-a0bf-b99e26a90668
-- title:
--   Equilibrium response $A_1$ of an informed farmer to her private signal
-- statement:
--   With $\Psi$ as in Proposition 1, an informed farmer's equilibrium quantity responds to her own private signal $x_i$ with the coefficient
--
--   $$
--   A_1=\frac{\gamma(2\alpha+\gamma)(n_1+1)}{b\Psi},
--   $$
--
--   display (7). It vanishes when $\gamma=0$ (no private signal).
--
--   **Formalization Note** $n$, $n_1$ are real; the denominator $b\Psi$ is positive for $b,\alpha>0$ and nonnegative $\beta,\gamma,n,n_1$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12

import Mathlib
import Definitions.Def_FarmerInfoProvision_Psi

namespace FarmerInfoProvision

/-- **The equilibrium response coefficient `A1`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12:
"`A1 = γ(2α + γ)(n1 + 1)/(bΨ)`", with `Ψ` as in `Psi`.

`A1` is the response of an informed farmer to her own private signal `x_i` in the
Bayesian Nash equilibrium of Proposition 1, when `n1` of the `n` farmers receive the public
signal.

**Formalization Note.** `n` and `n1` are real numbers (see `Psi`). For `b > 0`, `α > 0` and
nonnegative `β, γ, n, n1` the denominator `bΨ` is positive. -/
noncomputable def coefA1 (b n n1 α β γ : ℝ) : ℝ :=
  γ * (2 * α + γ) * (n1 + 1) / (b * Psi n n1 α β γ)

end FarmerInfoProvision


