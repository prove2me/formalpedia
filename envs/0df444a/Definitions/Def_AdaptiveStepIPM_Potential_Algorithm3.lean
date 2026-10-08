-- Prove2me | Definitions.Def_AdaptiveStepIPM_Potential_Algorithm3
-- name    : AdaptiveStepIPM_Potential_Algorithm3
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:48:28.197121+00:00
-- url     : https://prove2.me/theorems/b6b97f0c-47af-401f-b3c8-50cad4b9d077
-- title:
--   The parameter $\rho$ of Theorem 3 and the runs of Algorithm 3 (potential reduction in $\mathcal N_\infty^-(\beta)$)
-- statement:
--   The **primal–dual potential function** of Todd and Ye is
--   $$
--   \psi(x,s) = \rho\log(x^Ts) - \sum_{j=1}^n \log(x_j s_j), \qquad \rho > n, \tag{1}
--   $$
--   with $\log$ the natural logarithm. Theorem 3 fixes
--   $$
--   \rho := n + \Bigl(\frac{3}{\beta\gamma(1-\gamma)}\log\frac{1}{1-\beta}\Bigr) n^2 .
--   $$
--
--   **Algorithm 3.** Fix $\beta, \gamma \in (0,1)$, $\rho$, and a precision $t$, and let $\mathcal N = \mathcal N_\infty^-(\beta)$. Start from $(x^0, s^0) \in \mathcal N$ with $(x^0)^Ts^0 \le 2^t$ and $\psi(x^0, s^0) \le (\rho - n)t + n\log n$. While $(x^k)^Ts^k > 2^{-t}$: set $(x, s) = (x^k, s^k)$, compute a direction $d$ from (2) with parameter $\gamma$, choose $\bar\theta$ so that $(x(\bar\theta), s(\bar\theta)) \in \mathcal N$ and
--   $$
--   \psi(x(\bar\theta), s(\bar\theta)) \le \psi(x(\theta), s(\theta)) \quad\text{for each } \theta \text{ with } (x(\theta), s(\theta)) \in \mathcal N,
--   $$
--   and set $(x^{k+1}, s^{k+1}) = (x(\bar\theta), s(\bar\theta))$.
--
--   A **run** is a sequence $(x^k, s^k)_{k \ge 0}$ satisfying the start conditions and, for every $k$ with $(x^k)^Ts^k > 2^{-t}$, the step relation above from $(x^k, s^k)$ to $(x^{k+1}, s^{k+1})$. Unlike Algorithm 2, which takes the largest admissible step, Algorithm 3 takes the step that minimises the potential over the whole line within the neighbourhood.
--
--   **Formalization Note** $\psi$ is the published `LinearOptimization.interiorPointPotential ρ x s` $= \rho\log(s^Tx) - \sum_j\log x_j - \sum_j\log s_j$, which equals (1) at every pair with $x, s > 0$; here it is evaluated only at points of $\mathcal N_\infty^-(\beta) \subset \mathcal F^0$, which are strictly positive. The minimisation ranges over all real $\theta$ whose point lies in $\mathcal N$, exactly as printed, not over a segment $[0, \bar\theta]$. A minimiser need not exist (for instance when $n = 1$, or when $\psi$ is unbounded below along the line inside $\mathcal N$); an instance whose current iterate admits none has no run beyond that iterate. Iterates after the loop stops are unconstrained. $2^t$ and $2^{-t}$ are real powers with $t \in \mathbb R$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 3, (1); pp. 9–10, Algorithm 2; p. 11, §5, Algorithm 3 and ρ of Theorem 3

import Mathlib
import Definitions.Def_LinearOptimization_InteriorPointPotential
import Definitions.Def_AdaptiveStepIPM_Potential_Direction

/-!
Mizuno, Todd, Ye, Cornell ORIE TR 944 (1990, rev. 1991), §5 (p. 11), with the frame of
Algorithm 2 (§4, pp. 9–10).

The potential (1) `ψ(x, s) = ρ log(xᵀs) − Σⱼ log(x_j s_j)` is the published
`LinearOptimization.interiorPointPotential ρ x s = ρ log(sᵀx) − Σ log x_j − Σ log s_j`,
which agrees with (1) at every pair with `x, s > 0`; it is only ever evaluated at such pairs here.

Algorithm 3 is Algorithm 2 with `N = N_∞⁻(β)` except that the step `θ̄` is chosen so that
`(x(θ̄), s(θ̄)) ∈ N` and `ψ(x(θ̄), s(θ̄)) ≤ ψ(x(θ), s(θ))` for each `θ` with `(x(θ), s(θ)) ∈ N`.
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- The parameter of Theorem 3 (p. 11):
`ρ := n + (3/(βγ(1 − γ)) · log(1/(1 − β))) · n²`, with the natural logarithm. -/
noncomputable def rho (n : ℕ) (β γ : ℝ) : ℝ :=
  n + (3 / (β * γ * (1 - γ)) * Real.log (1 / (1 - β))) * (n : ℝ) ^ 2

/-- One iteration of Algorithm 3 (p. 11) from `(x, s)` to `(x', s')`: there is a solution
`d = (d_x, d_y, d_s)` of (2) at `(x, s)` with parameter `γ` and a step `θ̄` such that
`(x(θ̄), s(θ̄)) ∈ N_∞⁻(β)`, `ψ(x(θ̄), s(θ̄)) ≤ ψ(x(θ), s(θ))` for every real `θ` with
`(x(θ), s(θ)) ∈ N_∞⁻(β)`, and `(x', s') = (x(θ̄), s(θ̄))`. -/
def Alg3Step {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (β γ ρ : ℝ) (x s x' s' : Fin n → ℝ) : Prop :=
  ∃ (dx : Fin n → ℝ) (dy : Fin m → ℝ) (ds : Fin n → ℝ) (θbar : ℝ),
    IsNewtonDirection A γ x s dx dy ds ∧
    InNinfMinus A b c β (lineStep x dx θbar) (lineStep s ds θbar) ∧
    (∀ θ : ℝ, InNinfMinus A b c β (lineStep x dx θ) (lineStep s ds θ) →
      LinearOptimization.interiorPointPotential ρ (lineStep x dx θbar) (lineStep s ds θbar) ≤
        LinearOptimization.interiorPointPotential ρ (lineStep x dx θ) (lineStep s ds θ)) ∧
    x' = lineStep x dx θbar ∧ s' = lineStep s ds θbar

/-- A run of Algorithm 3 with precision `t` (pp. 9–11): the iterates `(x^k, s^k)` start in
`N_∞⁻(β)` with `(x⁰)ᵀs⁰ ≤ 2^t` (Algorithm 2's "Given" clause) and
`ψ(x⁰, s⁰) ≤ (ρ − n)t + n log n` (§5), and while `(x^k)ᵀs^k > 2^{−t}` the next iterate is
produced by one iteration of Algorithm 3. Iterates after the loop stops are unconstrained. -/
def IsAlg3Run {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (β γ ρ t : ℝ) (x s : ℕ → Fin n → ℝ) : Prop :=
  InNinfMinus A b c β (x 0) (s 0) ∧
  x 0 ⬝ᵥ s 0 ≤ (2 : ℝ) ^ t ∧
  LinearOptimization.interiorPointPotential ρ (x 0) (s 0) ≤
    (ρ - n) * t + n * Real.log n ∧
  ∀ k : ℕ, (2 : ℝ) ^ (-t) < x k ⬝ᵥ s k →
    Alg3Step A b c β γ ρ (x k) (s k) (x (k + 1)) (s (k + 1))

end AdaptiveStepIPM.Potential


