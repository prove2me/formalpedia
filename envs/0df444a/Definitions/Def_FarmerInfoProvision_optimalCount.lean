-- Prove2me | Definitions.Def_FarmerInfoProvision_optimalCount
-- name    : FarmerInfoProvision_optimalCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:34:30.863636+00:00
-- url     : https://prove2.me/theorems/1c5123d7-f0e6-4a0a-bb53-406b3b6bae39
-- title:
--   The policy $n_1^*$ named by Proposition 2 ($1$ if $V>0$, else $0$)
-- statement:
--   Proposition 2 names the optimal number of informed farmers
--
--   $$
--   n_1^*=\begin{cases}1 & \text{if } V(n,\beta;\gamma)>0,\\ 0 & \text{if } V(n,\beta;\gamma)\le 0.\end{cases}
--   $$
--
--   The definition only names this number; its optimality is the content of Proposition 2. At $V=0$ the policies $0$ and $1$ tie and the paper's choice $0$ is kept.
-- source:
--   Zhou, Fan, Chen, Tang, Information Provision and Farmer Welfare in Developing Economies, SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14

import Mathlib
import Definitions.Def_FarmerInfoProvision_provisionIndex

namespace FarmerInfoProvision

/-- **The optimal number `n1*` of informed farmers named by Proposition 2.**
Zhou, Fan, Chen, Tang, *Information Provision and Farmer Welfare in Developing Economies*,
SSRN 3369334 (June 27, 2019), §4.2, Proposition 2, p. 14: "The optimal information provision
policy `n1*` satisfies: `n1* = 1` if `V(n, β; γ) > 0`; `0` if `V(n, β; γ) ≤ 0`", with `V` as in
`provisionIndex`.

**Formalization Note.** The case split is the printed one: `V ≤ 0` (including `V = 0`, where
policies `0` and `1` tie) gives `0`. That this count is optimal is the content of Proposition 2;
the definition only names it. -/
noncomputable def optimalCount (n α β γ : ℝ) : ℕ :=
  if 0 < provisionIndex n α β γ then 1 else 0

end FarmerInfoProvision


