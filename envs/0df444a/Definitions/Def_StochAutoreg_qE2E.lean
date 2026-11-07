-- Prove2me | Definitions.Def_StochAutoreg_qE2E
-- name    : StochAutoreg_qE2E
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:16:21.899221+00:00
-- url     : https://prove2.me/theorems/242120e2-063e-4943-bb32-9984bca6e159
-- title:
--   End-to-end output probability $q_g^{\mathrm{e2e}-M}$
-- statement:
--   The **$M$-step end-to-end output probability** of $g$ at a prompt $x$ is the probability that the last generated token is $1$:
--
--   $$q_g^{\mathrm{e2e}-M}(x)=\Pr_g(Z_M=1\mid X=x)=\sum_{z\in\{0,1\}^M:\,z_M=1}P_g^M(z\mid x).$$
--
--   This is the target of chain-of-thoughts and end-to-end learning. For $M=1$ it equals $p_g$.
--
--   **Formalization Note** At $M=0$ the sum is empty; every statement assumes $M\ge1$.
-- source:
--   Doron-Arad–Mehalel–Mossel, Stochastic Autoregressive Learning, arXiv:2608.07224, §1.1, p.2

import Mathlib
import Definitions.Def_StochAutoreg_trajMass
import Definitions.Def_StochAutoreg_lastToken

namespace StochAutoreg

/-- The **`M`-step end-to-end output probability** `q_g^{e2e-M}(x) = Pr_g(Z_M = 1 | X = x)`: the total
mass of the trajectories from `x` whose last token is `1`.
Doron-Arad–Mehalel–Mossel, *Stochastic Autoregressive Learning*, arXiv:2608.07224, §1.1, p.2.

**Formalization Note.** The paper has `M ≥ 1`; at `M = 0` the value is `0` and every statement assumes
`1 ≤ M`. The trajectory sum is the primary definition; the backward recursion and the display
`q^{e2e-2}(x) = p(x)p(x1) + (1-p(x))p(x0)` of p.2 are proved in the verification file. -/
noncomputable def qE2E (g : Generator) (M : ℕ) (x : List Bool) : ℝ :=
  ∑ z : Fin M → Bool, if lastToken z = true then trajMass g M x z else 0

end StochAutoreg


