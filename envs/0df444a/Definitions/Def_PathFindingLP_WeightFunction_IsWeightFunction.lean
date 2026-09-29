-- Prove2me | Definitions.Def_PathFindingLP_WeightFunction_IsWeightFunction
-- name    : PathFindingLP_WeightFunction_IsWeightFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:45:48.697987+00:00
-- url     : https://prove2.me/theorems/c8cdfce8-2db1-4a9d-9581-2860f31e5310
-- title:
--   Weight function with constants $c_1, c_\gamma, c_r$ (Definition 4)
-- statement:
--   Let $A\in\mathbb R^{m\times n}$. For a map $g:\mathbb R^m_{>0}\to\mathbb R^m_{>0}$ from slacks to weights write $G(s)=\mathrm{diag}(g(s))$, let $G'(s)=J_s(g(s))$ be the Jacobian of $g$ at $s$, let $S=\mathrm{diag}(s)$, and let $\|y\|_{G(s)}=\sqrt{\sum_i g_i(s)\,y_i^2}$.
--
--   A **weight function** with constants $c_1,c_\gamma,c_r$ is a map $g$ that sends positive vectors to positive vectors, is differentiable at every $s\in\mathbb R^m_{>0}$, and satisfies for every $s\in\mathbb R^m_{>0}$:
--
--   1. **Size:** $\|g(s)\|_1\le c_1$.
--   2. **Slack sensitivity:** $c_\gamma\ge1$ and $\gamma(s,g(s))\le c_\gamma$, with $\gamma$ the slack sensitivity of Definition 2.
--   3. **Step consistency:** $c_r\ge1$, and for every $r\ge c_r$ and every $y\in\mathbb R^m$,
--   $$
--   \left\|\left(I+r^{-1}G(s)^{-1}G'(s)S\right)y\right\|_{G(s)}\le\|y\|_{G(s)},\qquad
--   \left\|y+r^{-1}G(s)^{-1}G'(s)Sy\right\|_\infty\le\|y\|_\infty+c_r\|y\|_{G(s)}.
--   $$
--   4. **Uniformity:** $\|g(s)\|_\infty\le2$.
--
--   Weight functions are the interface between the path-following framework (which re-centres with weights $g(s(x))$) and the particular choice of weights; the constants $c_1,c_\gamma,c_r$ control the iteration count.
--
--   **Formalization Note** The paper writes Size as "$c_1(g)=\|g(s)\|_1$" for all $s$; since the paper's own weight function has $\|g(s)\|_1=\tfrac32\mathrm{rank}(A)$ while Theorem 1 reports $c_1=2\,\mathrm{rank}(A)$, the constant is read as an upper bound. The first step-consistency bullet, an operator-norm bound $\|I+r^{-1}G^{-1}G'S\|_{G(s)}\le1$, is written as the equivalent inequality for every $y$. $G'(s)$ is `fderiv ℝ g s`, applied to $Sy$ = `fun j => s j * y j`; differentiability at every positive $s$ is part of the predicate, so the derivative is never the junk value $0$. $g$ is a function on all of $\mathbb R^m$, but every clause only looks at positive $s$ (an open set, so differentiability there depends only on the values of $g$ on the orthant). $\|\cdot\|_\infty$ is Mathlib's sup norm on `Fin m → ℝ`; $\|\cdot\|_1$ is $\sum_i|g_i(s)|$.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433 (DOI 10.1109/FOCS.2014.52), p. 428, §IV.C, Definition 4 (Weight Function), with G(s) and G'(s) as defined just above it

import Mathlib
import Definitions.Def_PathFindingLP_WeightFunction_SlackSensitivity

namespace PathFindingLP.WeightFunction

/-- The `G(s)`-norm `‖y‖_{G(s)} = √(∑ᵢ gᵢ yᵢ²)` for the weight vector `g = g(s)`. -/
noncomputable def gNorm {m : ℕ} (g y : Fin m → ℝ) : ℝ :=
  Real.sqrt (∑ i, g i * y i ^ 2)

/-- The vector `y + r⁻¹ G(s)⁻¹ G'(s) S y`, where `G(s) = diag(g(s))`, `S = diag(s)` and
`G'(s)` is the Jacobian (Fréchet derivative) of `g` at `s`. -/
noncomputable def consistencyStep {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ)) (s : Fin m → ℝ)
    (r : ℝ) (y : Fin m → ℝ) : Fin m → ℝ :=
  fun i => y i + r⁻¹ * ((fderiv ℝ g s (fun j => s j * y j)) i / g s i)

/-- The Step Consistency bullet of Definition 4 (Lee–Sidford 2014, §IV.C, p. 428) with
constant `cr`: `cr ≥ 1`, and for every `s > 0`, every `r ≥ cr` and every `y ∈ ℝ^m`,
`‖(I + r⁻¹ G⁻¹ G' S) y‖_{G(s)} ≤ ‖y‖_{G(s)}` (operator norm at most `1`) and
`‖y + r⁻¹ G⁻¹ G' S y‖_∞ ≤ ‖y‖_∞ + cr ‖y‖_{G(s)}`. The sup norm is Mathlib's norm on
`Fin m → ℝ`. -/
def IsStepConsistent {m : ℕ} (g : (Fin m → ℝ) → (Fin m → ℝ)) (cr : ℝ) : Prop :=
  1 ≤ cr ∧
    ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ r : ℝ, cr ≤ r → ∀ y : Fin m → ℝ,
      gNorm (g s) (consistencyStep g s r y) ≤ gNorm (g s) y ∧
        ‖consistencyStep g s r y‖ ≤ ‖y‖ + cr * gNorm (g s) y

/-- Definition 4 (Weight Function), Lee–Sidford 2014, §IV.C, p. 428: `g` maps positive vectors
to positive vectors and is differentiable at every positive `s`, and for all `s > 0`:
* Size: `‖g(s)‖₁ ≤ c₁`;
* Slack Sensitivity: `cγ ≥ 1` and `γ(s, g(s)) ≤ cγ`;
* Step Consistency: `IsStepConsistent g cr`;
* Uniformity: `‖g(s)‖_∞ ≤ 2`. -/
def IsWeightFunction {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (g : (Fin m → ℝ) → (Fin m → ℝ)) (c₁ cγ cr : ℝ) : Prop :=
  (∀ s : Fin m → ℝ, (∀ i, 0 < s i) → (∀ i, 0 < g s i) ∧ DifferentiableAt ℝ g s) ∧
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∑ i, |g s i| ≤ c₁) ∧
    (1 ≤ cγ ∧ ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → slackSensitivity A s (g s) ≤ cγ) ∧
    IsStepConsistent g cr ∧
    (∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ‖g s‖ ≤ 2)

end PathFindingLP.WeightFunction


