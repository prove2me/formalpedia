-- Prove2me | Definitions.Def_FarmerInfoProvision_OmegaD
-- name    : FarmerInfoProvision_OmegaD
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:01.204899+00:00
-- url     : https://prove2.me/theorems/0ad2ec86-cad7-4215-81e0-db0dabe3c6d0
-- title:
--   Denominator $\Omega_d(n_1,\beta;\gamma)$ of $\partial W/\partial n_1$
-- statement:
--   In the proof of Proposition 2 the derivative of the total welfare in a continuous $n_1$ is $\Omega_n/\Omega_d$, with
--
--   $$
--   \Omega_d(n_1,\beta;\gamma)=b\bigl\{4(1+n_1)\alpha^2+(1+n)\gamma(2\beta+\gamma+n_1\gamma)+2(1+n_1)\alpha\bigl[2\beta+(2+n)\gamma\bigr]\bigr\}^3,
--   $$
--
--   that is, $b\Psi^3$ with Proposition 1's $\Psi$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35

import Mathlib

namespace FarmerInfoProvision

/-- **The denominator `Ω_d(n1, β; γ)` of `∂W/∂n1` in the proof of Proposition 2.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35:
"`Ω_d(n1, β; γ) ≡ b{4(1 + n1)α² + (1 + n)γ(2β + γ + n1γ) + 2(1 + n1)α[2β + (2 + n)γ]}³`."

The bracket is Proposition 1's `Ψ` (p. 12), so `Ω_d = bΨ³`.

**Formalization Note.** `n` and `n1` are real numbers; the printed shape is kept. -/
noncomputable def OmegaD (b n n1 α β γ : ℝ) : ℝ :=
  b * (4 * (1 + n1) * α ^ 2 + (1 + n) * γ * (2 * β + γ + n1 * γ) +
    2 * (1 + n1) * α * (2 * β + (2 + n) * γ)) ^ 3

end FarmerInfoProvision


