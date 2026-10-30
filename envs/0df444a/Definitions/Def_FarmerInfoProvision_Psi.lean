-- Prove2me | Definitions.Def_FarmerInfoProvision_Psi
-- name    : FarmerInfoProvision_Psi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:29:27.392007+00:00
-- url     : https://prove2.me/theorems/b45d44b2-8543-47f6-8cd2-6cbb37396b0a
-- title:
--   Normalizing constant $\Psi$ of the equilibrium (Proposition 1)
-- statement:
--   For $n$ farmers of whom $n_1$ receive the public signal, with demand-shock precision $\alpha$, public-signal precision $\beta$ and private-signal precision $\gamma$, Proposition 1 normalizes the equilibrium coefficients by
--
--   $$
--   \Psi=4(n_1+1)\alpha^2+(n+1)\gamma\bigl[(n_1+1)\gamma+2\beta\bigr]+2(n_1+1)\alpha\bigl[(n+2)\gamma+2\beta\bigr].
--   $$
--
--   It is positive for $\alpha>0$ and nonnegative $\beta,\gamma,n,n_1$, and it is the base of the derivative denominator $\Omega_d=b\Psi^3$ in the proof of Proposition 2.
--
--   **Formalization Note** $n$ and $n_1$ are real numbers so that the proof of Proposition 2 can differentiate in $n_1$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, p. 12

import Mathlib

namespace FarmerInfoProvision

/-- **The normalizing constant `Ψ` of the Bayesian Nash equilibrium.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.1, Proposition 1, p. 12:
"`Ψ ≡ 4(n1 + 1)α² + (n + 1)γ[(n1 + 1)γ + 2β] + 2(n1 + 1)α[(n + 2)γ + 2β]`."

Here `n` is the number of farmers, `n1` the number of farmers who receive the public signal,
`α = 1/σ_u²` the precision of the demand shock, `β = 1/σ_r²` the precision of the public signal
and `γ = 1/σ_f²` the precision of each private signal.

**Formalization Note.** `n` and `n1` are real numbers so that the proof of Proposition 2 can
differentiate in `n1` (p. 35). For `α > 0`, `β, γ ≥ 0`, `n1 ≥ 0` and `n ≥ 0` the value is
positive. -/
noncomputable def Psi (n n1 α β γ : ℝ) : ℝ :=
  4 * (n1 + 1) * α ^ 2 + (n + 1) * γ * ((n1 + 1) * γ + 2 * β) +
    2 * (n1 + 1) * α * ((n + 2) * γ + 2 * β)

end FarmerInfoProvision


