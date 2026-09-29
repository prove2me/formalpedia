-- Prove2me | Definitions.Def_ThreeOpSplitting_Accel_Stepsizes
-- name    : ThreeOpSplitting_Accel_Stepsizes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:58:06.518973+00:00
-- url     : https://prove2.me/theorems/da103d7f-5417-4cde-beb9-742e95b2d2f5
-- title:
--   The accelerated stepsize rules (3.6) and (3.7)
-- statement:
--   Two stepsize sequences, each defined recursively from an initial stepsize $\gamma_0$.
--
--   1. **Rule (3.6)** (Theorem 3.3, Part 1), with parameters $\mu_B, \mu_C, \eta$: for $k \ge 0$,
--   $$\gamma_{k+1} = \frac{-2\gamma_k^2\mu_C\eta + \sqrt{(2\gamma_k^2\mu_C\eta)^2 + 4(1 + 2\gamma_k\mu_B)\gamma_k^2}}{2(1 + 2\gamma_k\mu_B)}.$$
--   2. **Rule (3.7)** (Theorem 3.3, Part 2), with parameters $\mu_B, L_C$: for $k \ge 0$,
--   $$\gamma_{k+1} = \frac{\gamma_k}{\sqrt{1 + 2\gamma_k(\mu_B - \gamma_k L_C^2/2)}}.$$
--
--   Rule (3.6) makes $\gamma_{k+1}$ the positive root of $(1+2\gamma_k\mu_B)\gamma^2 + 2\gamma_k^2\mu_C\eta\,\gamma - \gamma_k^2 = 0$. Both rules produce stepsizes decreasing like $1/k$, which is what yields the $O(1/(k+1)^2)$ rate of Theorem 3.3.
--
--   **Formalization Note** The sequences are defined for all real parameters, using Lean's total square root (which returns $0$ on negative input) and total division; every theorem using them assumes the paper's parameter ranges ($\gamma_0 > 0$, $\mu_B \ge 0$, $\mu_C > 0$, $\eta \in (0,1)$ for (3.6); $\mu_B > 0$, $L_C > 0$, $\gamma_0 \in (0, 2\mu_B/L_C^2)$ for (3.7)), under which the square roots have positive arguments and the denominators are positive.
-- source:
--   Davis and Yin, A Three-Operator Splitting Scheme and its Optimization Applications, Set-Valued Var. Anal. 25 (2017), https://doi.org/10.1007/s11228-017-0421-z, p. 842, Theorem 3.3, Eq. (3.6) and Eq. (3.7)

import Mathlib

namespace ThreeOpSplitting.Accel

/-- The stepsize rule (3.6) of Theorem 3.3, Part 1: `γ_0 = γ0` and, for `k ≥ 0`,
`γ_{k+1} = (-2γ_k²μ_Cη + √((2γ_k²μ_Cη)² + 4(1 + 2γ_kμ_B)γ_k²)) / (2(1 + 2γ_kμ_B))`. -/
noncomputable def stepsPart1 (μB μC η γ0 : ℝ) : ℕ → ℝ
  | 0 => γ0
  | k + 1 =>
    let g := stepsPart1 μB μC η γ0 k
    (-2 * g ^ 2 * μC * η + Real.sqrt ((2 * g ^ 2 * μC * η) ^ 2 + 4 * (1 + 2 * g * μB) * g ^ 2))
      / (2 * (1 + 2 * g * μB))

/-- The stepsize rule (3.7) of Theorem 3.3, Part 2: `γ_0 = γ0` and, for `k ≥ 0`,
`γ_{k+1} = γ_k / √(1 + 2γ_k(μ_B - γ_k L_C²/2))`. -/
noncomputable def stepsPart2 (μB LC γ0 : ℝ) : ℕ → ℝ
  | 0 => γ0
  | k + 1 =>
    let g := stepsPart2 μB LC γ0 k
    g / Real.sqrt (1 + 2 * g * (μB - g * LC ^ 2 / 2))

end ThreeOpSplitting.Accel


