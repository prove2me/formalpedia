-- Prove2me | Definitions.Def_FarmerInfoProvision_profitInformed
-- name    : FarmerInfoProvision_profitInformed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:32:00.102203+00:00
-- url     : https://prove2.me/theorems/3f8a8427-12c7-4178-8aaf-5a1e8ed4609b
-- title:
--   Lemma 2's ex-ante profit $W^I(n_1,\beta;\gamma)$ of an informed farmer (closed form)
-- statement:
--   With the equilibrium coefficients $A_0,A_1,A_2$ of Proposition 1, Lemma 2 gives the ex-ante expected profit of a farmer who receives the public signal as
--
--   $$
--   W^I(n_1,\beta;\gamma)=b\Bigl\{A_0^2+A_1^2\Bigl(\frac1\alpha+\frac1\gamma\Bigr)+A_2^2\Bigl(\frac1\alpha+\frac1\beta\Bigr)+2A_1A_2\frac1\alpha\Bigr\}.
--   $$
--
--   This definition is the closed form only; that it is the equilibrium profit in the game is milestone Lemma 2.
--
--   **Formalization Note** At $\gamma=0$ the term $1/\gamma$ is Lean's junk value $1/0=0$, but it is always multiplied by a coefficient that vanishes at $\gamma=0$, so the formula takes its $\gamma\to0$ limit. At $\gamma=0$ the value is $b\{A_0^2+A_2^2(1/\alpha+1/\beta)\}$.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14

import Mathlib
import Definitions.Def_FarmerInfoProvision_coefA0
import Definitions.Def_FarmerInfoProvision_coefA1
import Definitions.Def_FarmerInfoProvision_coefA2

namespace FarmerInfoProvision

/-- **Lemma 2's ex-ante expected profit `W^I(n1, β; γ)` of a farmer with access to the public
signal.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Lemma 2, p. 14:
"`W^I(n1, β; γ) = b{A0² + A1²(1/α + 1/γ) + A2²(1/α + 1/β) + 2A1A2(1/α)}`",
with `A0`, `A1`, `A2` as in Proposition 1 (`coefA0`, `coefA1`, `coefA2`).

This is the closed form only; that it equals the equilibrium expected profit of an informed
farmer in the game of §3 is the content of Lemma 2 (milestone
`FarmerInfoProvision.lemma_2_ex_ante_profits`).

**Formalization Note.** `n` and `n1` are real numbers (see `Psi`). At `γ = 0` (no private
signal, p. 9) Lean's `1/0 = 0` makes `1/γ` a junk value, but it is multiplied by
`A1² = 0` (`coefA1` has the factor `γ`), so the value is
`b(A0² + A2²(1/α + 1/β))`, the `γ → 0` limit of the formula. -/
noncomputable def profitInformed (a b c n n1 α β γ : ℝ) : ℝ :=
  b * (coefA0 a b c n ^ 2 + coefA1 b n n1 α β γ ^ 2 * (1 / α + 1 / γ) +
    coefA2 b n n1 α β γ ^ 2 * (1 / α + 1 / β) +
    2 * coefA1 b n n1 α β γ * coefA2 b n n1 α β γ * (1 / α))

end FarmerInfoProvision


