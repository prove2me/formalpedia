-- Prove2me | Definitions.Def_PrideGuilt_optProfit
-- name    : PrideGuilt_optProfit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:00:09.78304+00:00
-- url     : https://prove2.me/theorems/d08fcb7c-92f4-40b6-a5e6-daa208b4cea8
-- title:
--   Optimal profit $\Pi^*(\gamma_P,\gamma_G)$ over prices and rewards with nonnegative demand
-- statement:
--   For fixed parameters, the manufacturer's optimal profit is
--
--   $$
--   \Pi^*(\gamma_P,\gamma_G)=\sup\{\Pi(p,f) : (p,f)\in\mathbb R^2,\ D(p,f)\ge0\},
--   $$
--
--   viewed as a function of the social pride $\gamma_P$ and guilt $\gamma_G$. This is the quantity whose partial derivatives Theorem 2 signs.
--
--   **Formalization Note** Eq. (5) prints $\max_{p,f}$ without constraint. Without $D\ge0$ a negative demand times a negative margin counts as profit and the maximum is $+\infty$ (take $\tau^*=1$, $f\to\infty$, $b_0>b_1$); the paper's own model requires feasible demand (footnote 4, p.13: $D(p^*,f^*)\in[0,1]$; p.12: "a feasible and profitable market"). The bound $D\le1$ is not imposed. Prices and rewards range over all of $\mathbb R$, as in (5). The value is a supremum of reals; the Proposition 5 milestone shows it is attained in $\Omega_4$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), eq. (5), p.12

import Mathlib
import Definitions.Def_PrideGuilt_profit

namespace PrideGuilt

/-- **The manufacturer's optimal profit (5), `Π*(γ_P, γ_G)`, over prices and rewards with
nonnegative demand.**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, eq. (5), p.12 (PDF 13).

`Π*(γ_P, γ_G) = sup {Π(p, f) : (p, f) ∈ ℝ², D(p, f) ≥ 0}`, a function of the pride and guilt
parameters with every other parameter fixed.

**Formalization Note.** (5) prints `max_{p,f}` with no constraint. Without `D ≥ 0` a negative
demand times a negative margin counts as profit and the printed maximum is `+∞` (take `τ* = 1`,
`f → ∞`, `b₀ > b₁`); the constraint is the paper's own model (footnote 4, p.13: `D(p*, f*) ∈ [0, 1]`;
p.12: "a feasible and profitable market"). The upper bound `D ≤ 1` is not imposed. `p` and `f`
range over all of `ℝ`, as in (5). The value is `sSup` of a set of reals; it is the maximum
wherever the theorems prove the set has a greatest element (`proposition_5`). -/
noncomputable def optProfit (P : Params) (γP γG : ℝ) : ℝ :=
  sSup {π : ℝ | ∃ p f : ℝ, 0 ≤ demand P γP γG p f ∧ π = profit P γP γG p f}

end PrideGuilt


