-- Prove2me | Definitions.Def_FarmerInfoProvision_profitUninformed
-- name    : FarmerInfoProvision_profitUninformed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:28.273607+00:00
-- url     : https://prove2.me/theorems/93bbc97e-9520-429a-99e5-8d6858dee4cc
-- title:
--   Lemma 2's ex-ante profit $W^J(n_1,\beta;\gamma)$ of an uninformed farmer (closed form)
-- statement:
--   With the equilibrium coefficients $B_0=A_0$ and $B_1$ of Proposition 1, Lemma 2 gives the ex-ante expected profit of a farmer without the public signal as
--
--   $$
--   W^J(n_1,\beta;\gamma)=b\Bigl\{B_0^2+B_1^2\Bigl(\frac1\alpha+\frac1\gamma\Bigr)\Bigr\}.
--   $$
--
--   This definition is the closed form only; that it is the equilibrium profit in the game is milestone Lemma 2.
--
--   **Formalization Note** At $\gamma=0$ the term $1/\gamma$ is Lean's junk value $1/0=0$, but it is always multiplied by a coefficient that vanishes at $\gamma=0$, so the formula takes its $\gamma\to0$ limit. At $\gamma=0$ the value is $bA_0^2$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14

import Mathlib
import Definitions.Def_FarmerInfoProvision_coefA0
import Definitions.Def_FarmerInfoProvision_coefB1

namespace FarmerInfoProvision

/-- **Lemma 2's ex-ante expected profit `W^J(n1, β; γ)` of a farmer without access to the public
signal.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14:
"`W^J(n1, β; γ) = b{B0² + B1²(1/α + 1/γ)}`", with `B0 = A0` and `B1` as in Proposition 1
(display (7), p. 12; `coefA0`, `coefB1`).

This is the closed form only; that it equals the equilibrium expected profit of an uninformed
farmer in the game of §3 is the content of Lemma 2 (milestone
`FarmerInfoProvision.lemma_2_ex_ante_profits`).

**Formalization Note.** `B0` is written `coefA0` since `A0 = B0` by (7). At `γ = 0` the junk
value of `1/γ` is multiplied by `B1² = 0`, so the value is `b·A0²`, the `γ → 0` limit. -/
noncomputable def profitUninformed (a b c n n1 α β γ : ℝ) : ℝ :=
  b * (coefA0 a b c n ^ 2 + coefB1 b n n1 α β γ ^ 2 * (1 / α + 1 / γ))

end FarmerInfoProvision


