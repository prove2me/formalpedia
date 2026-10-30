-- Prove2me | Definitions.Def_FarmerInfoProvision_coefA2
-- name    : FarmerInfoProvision_coefA2
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:30:54.476892+00:00
-- url     : https://prove2.me/theorems/3eaf2c0a-a72b-4bb6-aa74-6218d31167c8
-- title:
--   Equilibrium response $A_2$ of an informed farmer to the public signal
-- statement:
--   With $\Psi$ as in Proposition 1, an informed farmer's equilibrium quantity responds to the public signal $y$ with the coefficient
--
--   $$
--   A_2=\frac{2\beta(2\alpha+\gamma)}{b\Psi},
--   $$
--
--   display (7).
--
--   **Formalization Note** $n$, $n_1$ are real; the denominator $b\Psi$ is positive for $b,\alpha>0$ and nonnegative $\beta,\gamma,n,n_1$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12

import Mathlib
import Definitions.Def_FarmerInfoProvision_Psi

namespace FarmerInfoProvision

/-- **The equilibrium response coefficient `A2`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12:
"`A2 = 2β(2α + γ)/(bΨ)`", with `Ψ` as in `Psi`.

`A2` is the response of an informed farmer to the public signal `y` in the
Bayesian Nash equilibrium of Proposition 1, when `n1` of the `n` farmers receive the public
signal.

**Formalization Note.** `n` and `n1` are real numbers (see `Psi`). For `b > 0`, `α > 0` and
nonnegative `β, γ, n, n1` the denominator `bΨ` is positive. -/
noncomputable def coefA2 (b n n1 α β γ : ℝ) : ℝ :=
  2 * β * (2 * α + γ) / (b * Psi n n1 α β γ)

end FarmerInfoProvision


