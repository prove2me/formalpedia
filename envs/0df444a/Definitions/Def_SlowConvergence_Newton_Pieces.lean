-- Prove2me | Definitions.Def_SlowConvergence_Newton_Pieces
-- name    : SlowConvergence_Newton_Pieces
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:38:55.318324+00:00
-- url     : https://prove2.me/theorems/72f0260b-1770-454d-ac40-27947cad25cd
-- title:
--   The Hermite quintics $p_k$ (2.11), (2.14) at $\alpha_k = 1$ and $q_k$ (p. 8), and the knot values (3.9)–(3.10)
-- statement:
--   With $\eta$, $\mu_k$ and $\zeta$ as in the data of the example, let
--   $$\psi_k = \Big(\frac{k+1}{k+2}\Big)^{\frac12+\eta}, \qquad \phi_k = -\psi_k ,$$
--   which is $\phi_k = \frac{1}{\alpha_k}(1-\alpha_k-\psi_k)$ of (2.15) in the case $\alpha_k = 1$.
--
--   The first-coordinate piece is the quintic of (2.11) with the coefficients of p. 4 and (2.14) at $\alpha_k = 1$:
--   $$p_k(t) = \tfrac12\Big(\frac1{k+1}\Big)^{1+2\eta} - \mu_k t + \tfrac12 t^2 - 4\frac{\phi_k}{\mu_k} t^3 + 7\frac{\phi_k}{\mu_k^2} t^4 - 3\frac{\phi_k}{\mu_k^3} t^5 ,$$
--   used on $[0,\mu_k]$. The second-coordinate piece is the quintic of pp. 7–8,
--   $$q_k(t) = d_{0,k} + d_{1,k}t + \dots + d_{5,k}t^5,$$
--   used on $[0,1]$, with $d_{0,k} = \tfrac12 b_k$, $d_{1,k} = -b_k$, $d_{2,k} = \tfrac12 b_k$ and
--   $$(d_{3,k}, d_{4,k}, d_{5,k}) = \tfrac12\big(9c_k - b_k,\; -16c_k + 2b_k,\; 7c_k - b_k\big),$$
--   where $b_k = (1/(k+1))^2$ and $c_k = (1/(k+2))^2$.
--
--   Finally, the knot values of the two coordinate functions are defined by the recursions (3.9) and (3.10):
--   $$f_{2,1}([x_0]_1) = \tfrac12\zeta(1+2\eta), \qquad f_{2,1}([x_{k+1}]_1) = f_{2,1}([x_k]_1) - \tfrac12\Big(\frac1{k+1}\Big)^{1+2\eta},$$
--   $$f_{2,2}([x_0]_2) = \tfrac12\zeta(2), \qquad f_{2,2}([x_{k+1}]_2) = f_{2,2}([x_k]_2) - \tfrac12\Big(\frac1{k+1}\Big)^{2}.$$
--
--   The function of the example is $f_2(x) = f_{2,1}([x]_1) + f_{2,2}([x]_2)$, where $f_{2,1}$ is $p_k$ translated to the $k$-th interval of the first coordinate and shifted by the next knot value, and $f_{2,2}$ is $q_k$ translated to $[k, k+1]$ likewise. These pieces are the building blocks of the milestones; the goal theorem does not mention them.
--
--   **Formalization Note** $p_k$ and $q_k$ are the polynomial functions on all of $\mathbb R$; the intervals on which the paper uses them appear in the milestone statements. The knot values are indexed by $k$: `f21knot τ k` is $f_{2,1}([x_k]_1)$ and `f22knot k` is $f_{2,2}([x_k]_2)$.
-- source:
--   Cartis, Gould & Toint, On the complexity of steepest descent, Newton's and regularized Newton's methods, preprint 15 Oct 2009, p. 4, §2, (2.11)–(2.15); p. 7, §3, (3.9)–(3.10) and f_{2,1} = f_1 with α_k = 1; pp. 7–8, q_k and (d_{3,k}, d_{4,k}, d_{5,k})

import Mathlib
import Definitions.Def_SlowConvergence_Newton_Data
import Definitions.Def_SlowConvergence_SteepestDescent_Hermite

namespace SlowConvergence.Newton

/-- `φ_k = (1/α_k)(1 − α_k − ψ_k)` of (2.15), p. 4, in the case `α_k = 1` used for `f_{2,1}` (p. 7),
where it reduces to `φ_k = −ψ_k`. -/
noncomputable def phi (τ : ℝ) (k : ℕ) : ℝ := -SlowConvergence.SteepestDescent.psi τ k

/-- The quintic Hermite piece `p_k(t) = c_{0,k} + c_{1,k} t + … + c_{5,k} t⁵` of (2.11), p. 4, with the
coefficients of p. 4 and (2.14) at `α_k = 1` (the choice `f_{2,1} = f_1` with `α_k = 1`, p. 7):
`c_{0,k} = ½(1/(k+1))^{1+2η}`, `c_{1,k} = −(1/(k+1))^{1/2+η}`, `c_{2,k} = ½`,
`c_{3,k} = −4φ_k/µ_k`, `c_{4,k} = 7φ_k/µ_k²`, `c_{5,k} = −3φ_k/µ_k³`, with `µ_k = (1/(k+1))^{1/2+η}`.
It is used on `[0, µ_k]`; here it is the polynomial function on all of `ℝ`. -/
noncomputable def p (τ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ)
    + (-mu τ k) * t
    + 1 / 2 * t ^ 2
    + (-4 * phi τ k / mu τ k) * t ^ 3
    + (7 * phi τ k / mu τ k ^ 2) * t ^ 4
    + (-3 * phi τ k / mu τ k ^ 3) * t ^ 5

/-- The quintic piece `q_k(t) = d_{0,k} + d_{1,k} t + … + d_{5,k} t⁵` of §3, pp. 7–8, with
`d_{0,k} = ½(1/(k+1))²`, `d_{1,k} = −(1/(k+1))²`, `d_{2,k} = ½(1/(k+1))²` and
`(d_{3,k}, d_{4,k}, d_{5,k}) = ½(9(1/(k+2))² − (1/(k+1))², −16(1/(k+2))² + 2(1/(k+1))², 7(1/(k+2))² − (1/(k+1))²)`.
It is used on `[0, 1]`; here it is the polynomial function on all of `ℝ`. -/
noncomputable def q (k : ℕ) (t : ℝ) : ℝ :=
  1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2
    + (-((1 / ((k : ℝ) + 1)) ^ 2)) * t
    + 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2 * t ^ 2
    + 1 / 2 * (9 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2) * t ^ 3
    + 1 / 2 * (-16 * (1 / ((k : ℝ) + 2)) ^ 2 + 2 * (1 / ((k : ℝ) + 1)) ^ 2) * t ^ 4
    + 1 / 2 * (7 * (1 / ((k : ℝ) + 2)) ^ 2 - (1 / ((k : ℝ) + 1)) ^ 2) * t ^ 5

/-- The knot values (3.9), p. 7, of the first-coordinate function `f_{2,1}`:
`f_{2,1}(0) = ½ζ(1 + 2η)` and `f_{2,1}([x_{k+1}]_1) = f_{2,1}([x_k]_1) − ½(1/(k+1))^{1+2η}`.
`f21knot τ k` is the value `f_{2,1}([x_k]_1)`. -/
noncomputable def f21knot (τ : ℝ) : ℕ → ℝ
  | 0 => 1 / 2 * zetaR (1 + 2 * eta τ)
  | k + 1 => f21knot τ k - 1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * eta τ)

/-- The knot values (3.10), p. 7, of the second-coordinate function `f_{2,2}`:
`f_{2,2}(0) = ½ζ(2)` and `f_{2,2}([x_{k+1}]_2) = f_{2,2}([x_k]_2) − ½(1/(k+1))²`.
`f22knot k` is the value `f_{2,2}([x_k]_2) = f_{2,2}(k)`. -/
noncomputable def f22knot : ℕ → ℝ
  | 0 => 1 / 2 * zetaR 2
  | k + 1 => f22knot k - 1 / 2 * (1 / ((k : ℝ) + 1)) ^ 2

end SlowConvergence.Newton


