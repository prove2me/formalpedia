-- Prove2me | Definitions.Def_FarmerInfoProvision_OmegaN
-- name    : FarmerInfoProvision_OmegaN
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:41.812008+00:00
-- url     : https://prove2.me/theorems/ddc4316b-0704-43f2-825b-a104e305b524
-- title:
--   Numerator $\Omega_n(n_1,\beta;\gamma)$ of $\partial W/\partial n_1$
-- statement:
--   In the proof of Proposition 2 the derivative of the total welfare in a continuous $n_1$ is $\Omega_n/\Omega_d$, with
--
--   $$
--   \begin{aligned}
--   \Omega_n(n_1,\beta;\gamma)=-4\beta\Bigl\{&16(-1+n_1)\alpha^4+8\alpha^3\bigl(4(-1+n_1)\beta+(-5+3n_1+2n_1n)\gamma\bigr)\\
--   &+\gamma^2\bigl(2(-3+n)\beta^2+(-7-n_1+n+3n_1n)\beta\gamma+2(-1+n_1n)\gamma^2\bigr)\\
--   &+4\alpha^2\bigl(4(-1+n_1)\beta^2+(-15+9n_1+4n_1n)\beta\gamma+3(-3+n_1+2n_1n)\gamma^2\bigr)\\
--   &+2\alpha\gamma\bigl(2(-5+3n_1)\beta^2+(-18+4n_1+n+7n_1n)\beta\gamma+(-7+n_1+6n_1n)\gamma^2\bigr)\Bigr\}.
--   \end{aligned}
--   $$
--
--   It is affine in $n_1$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35

import Mathlib

namespace FarmerInfoProvision

/-- **The numerator `Ω_n(n1, β; γ)` of `∂W/∂n1` in the proof of Proposition 2.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), Appendix A, proof of Proposition 2, unnumbered display, p. 35:
"`Ω_n(n1, β; γ) ≡ −4β{16(−1 + n1)α⁴ + 8α³(4(−1 + n1)β + (−5 + 3n1 + 2n1n)γ)
+ γ²(2(−3 + n)β² + (−7 − n1 + n + 3n1n)βγ + 2(−1 + n1n)γ²)
+ 4α²(4(−1 + n1)β² + (−15 + 9n1 + 4n1n)βγ + 3(−3 + n1 + 2n1n)γ²)
+ 2αγ(2(−5 + 3n1)β² + (−18 + 4n1 + n + 7n1n)βγ + (−7 + n1 + 6n1n)γ²)}`."

**Formalization Note.** `n` and `n1` are real numbers (the proof treats `n1` as continuous). -/
noncomputable def OmegaN (n n1 α β γ : ℝ) : ℝ :=
  -4 * β * (16 * (-1 + n1) * α ^ 4 +
    8 * α ^ 3 * (4 * (-1 + n1) * β + (-5 + 3 * n1 + 2 * n1 * n) * γ) +
    γ ^ 2 * (2 * (-3 + n) * β ^ 2 + (-7 - n1 + n + 3 * n1 * n) * β * γ +
      2 * (-1 + n1 * n) * γ ^ 2) +
    4 * α ^ 2 * (4 * (-1 + n1) * β ^ 2 + (-15 + 9 * n1 + 4 * n1 * n) * β * γ +
      3 * (-3 + n1 + 2 * n1 * n) * γ ^ 2) +
    2 * α * γ * (2 * (-5 + 3 * n1) * β ^ 2 + (-18 + 4 * n1 + n + 7 * n1 * n) * β * γ +
      (-7 + n1 + 6 * n1 * n) * γ ^ 2))

end FarmerInfoProvision


