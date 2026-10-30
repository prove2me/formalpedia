-- Prove2me | Definitions.Def_FarmerInfoProvision_coefB1
-- name    : FarmerInfoProvision_coefB1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:31:26.888244+00:00
-- url     : https://prove2.me/theorems/29577bdc-62c1-4324-8e84-be3c7aa6a6a7
-- title:
--   Equilibrium response $B_1$ of an uninformed farmer to her private signal
-- statement:
--   With $\Psi$ as in Proposition 1, an uninformed farmer's equilibrium quantity responds to her own private signal $x_j$ with the coefficient
--
--   $$
--   B_1=\frac{\gamma\bigl[(n_1+1)(2\alpha+\gamma)+2\beta\bigr]}{b\Psi},
--   $$
--
--   display (7). It vanishes when $\gamma=0$.
--
--   **Formalization Note** $n$, $n_1$ are real; the denominator $b\Psi$ is positive for $b,\alpha>0$ and nonnegative $\beta,\gamma,n,n_1$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12

import Mathlib
import Definitions.Def_FarmerInfoProvision_Psi

namespace FarmerInfoProvision

/-- **The equilibrium response coefficient `B1`.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, display (7), p. 12:
"`B1 = γ[(n1 + 1)(2α + γ) + 2β]/(bΨ)`", with `Ψ` as in `Psi`.

`B1` is the response of an uninformed farmer to her own private signal `x_j` in the
Bayesian Nash equilibrium of Proposition 1, when `n1` of the `n` farmers receive the public
signal.

**Formalization Note.** `n` and `n1` are real numbers (see `Psi`). For `b > 0`, `α > 0` and
nonnegative `β, γ, n, n1` the denominator `bΨ` is positive. -/
noncomputable def coefB1 (b n n1 α β γ : ℝ) : ℝ :=
  γ * ((n1 + 1) * (2 * α + γ) + 2 * β) / (b * Psi n n1 α β γ)

end FarmerInfoProvision


