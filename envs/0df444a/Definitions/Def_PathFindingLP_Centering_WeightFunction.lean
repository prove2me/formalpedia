-- Prove2me | Definitions.Def_PathFindingLP_Centering_WeightFunction
-- name    : PathFindingLP_Centering_WeightFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T22:36:21.453309+00:00
-- url     : https://prove2.me/theorems/3feb9355-d8b2-457f-a185-f278a7946d47
-- title:
--   Definition 4 (Weight Function): size $c_1$, slack sensitivity $c_\gamma$, step consistency $c_r$, uniformity
-- statement:
--   Let $A\in\mathbb R^{m\times n}$. A **weight function** for $A$ is a differentiable map $\vec g:\mathbb R^m_{>0}\to\mathbb R^m_{>0}$ from slack vectors to positive weights, together with constants $c_1,c_\gamma,c_r$, such that for every $s\in\mathbb R^m_{>0}$, writing $G(s)=\mathrm{diag}(\vec g(s))$, $G'(s)=J_s(\vec g(s))$ for the Jacobian of $\vec g$ at $s$, $S=\mathrm{diag}(s)$ and $\|y\|_{G(s)}=\sqrt{\sum_i g_i(s)\,y_i^2}$:
--
--   1. **Size:** $\|\vec g(s)\|_1\le c_1$.
--   2. **Slack sensitivity:** $c_\gamma\ge1$ and $\gamma(s,\vec g(s))\le c_\gamma$, with $\gamma$ the slack sensitivity of Definition 2.
--   3. **Step consistency:** $c_r\ge1$, and for every $r\ge c_r$ and every $y\in\mathbb R^m$,
--   $$\big\|\big(I+r^{-1}G(s)^{-1}G'(s)S\big)y\big\|_{G(s)}\le\|y\|_{G(s)},\qquad \big\|y+r^{-1}G(s)^{-1}G'(s)Sy\big\|_\infty\le\|y\|_\infty+c_r\|y\|_{G(s)}.$$
--   4. **Uniformity:** $\|\vec g(s)\|_\infty\le2$.
--
--   A weight function is the device that lets the path-following method re-weight the barrier after every step: it keeps the slack sensitivity bounded (so Newton steps converge quickly) while the step-consistency conditions ensure that resetting the weights to $\vec g(s)$ after a step does not destroy centrality.
--
--   **Formalization Note** The page writes the size condition as "$c_1(\vec g)=\|\vec g(s)\|_1$"; since it quantifies over all $s$ and the paper's own weight function (§V) has $\|\vec g(s)\|_1$ strictly below the $c_1$ it reports, the condition is read as the upper bound $\|\vec g(s)\|_1\le c_1$. The first step-consistency condition, an operator-norm bound $\|I+r^{-1}G^{-1}G'S\|_{G(s)}\le1$, is written as the equivalent inequality for every $y$. $\vec g$ is a total function on $\mathbb R^m$; only its values and differentiability at positive $s$ are constrained, and $G'(s)$ is the Fréchet derivative `fderiv ℝ g s`. $\|\cdot\|_\infty$ is Mathlib's sup norm on `Fin m → ℝ`. The predicate depends on $A$ through $\gamma$.
-- source:
--   Lee, Sidford, Path Finding Methods for Linear Programming, FOCS 2014, pp. 424–433, p. 428, §IV.C, Definition 4 (Weight Function), with G(s) and G'(s) as defined in the paragraph above it

import Mathlib
import Definitions.Def_PathFindingLP_Centering_SlackSensitivity

open Matrix

namespace PathFindingLP.Centering

variable {m n : ℕ}

/-- The weighted norm `‖y‖_{G} = √(∑ᵢ gᵢ yᵢ²)` of `G = diag(g)`. -/
noncomputable def diagNorm {k : ℕ} (g y : Fin k → ℝ) : ℝ :=
  Real.sqrt (∑ i, g i * y i ^ 2)

/-- The vector `G(s)⁻¹ G'(s) S y`, where `G(s) = diag(g(s))`, `G'(s) = J_s(g(s))` is the Jacobian
of `g` at `s` (the Fréchet derivative `fderiv ℝ g s`), and `S = diag(s)`. -/
noncomputable def jacobianTerm (g : (Fin m → ℝ) → (Fin m → ℝ)) (s y : Fin m → ℝ) :
    Fin m → ℝ :=
  fun i => (g s i)⁻¹ * fderiv ℝ g s (fun j => s j * y j) i

/-- Definition 4 (Weight Function), §IV.C, p. 428, relative to the constraint matrix `A`.
`g : ℝᵐ_{>0} → ℝᵐ_{>0}` is differentiable, and for constants `c₁, c_γ, c_r` and all
`s ∈ ℝᵐ_{>0}`:
* Size: `‖g(s)‖₁ ≤ c₁` (read as an upper bound, see the natural-language statement);
* Slack Sensitivity: `c_γ ≥ 1` and `γ(s, g(s)) ≤ c_γ`;
* Step Consistency: `c_r ≥ 1` and for all `r ≥ c_r` and all `y ∈ ℝᵐ`,
  `‖(I + r⁻¹ G(s)⁻¹ G'(s) S) y‖_{G(s)} ≤ ‖y‖_{G(s)}` and
  `‖y + r⁻¹ G(s)⁻¹ G'(s) S y‖_∞ ≤ ‖y‖_∞ + c_r ‖y‖_{G(s)}`;
* Uniformity: `‖g(s)‖_∞ ≤ 2`.
Here `‖·‖_∞` on `Fin m → ℝ` is Mathlib's sup norm `‖·‖`. -/
structure IsWeightFunction (A : Matrix (Fin m) (Fin n) ℝ) (g : (Fin m → ℝ) → (Fin m → ℝ))
    (c₁ cγ cr : ℝ) : Prop where
  pos : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ i, 0 < g s i
  differentiableAt : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → DifferentiableAt ℝ g s
  size : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∑ i, |g s i| ≤ c₁
  one_le_cγ : 1 ≤ cγ
  slackSensitivity_le : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → slackSensitivity A s (g s) ≤ cγ
  one_le_cr : 1 ≤ cr
  stepConsistency_op : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ r : ℝ, cr ≤ r → ∀ y : Fin m → ℝ,
    diagNorm (g s) (y + r⁻¹ • jacobianTerm g s y) ≤ diagNorm (g s) y
  stepConsistency_inf : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ∀ r : ℝ, cr ≤ r → ∀ y : Fin m → ℝ,
    ‖y + r⁻¹ • jacobianTerm g s y‖ ≤ ‖y‖ + cr * diagNorm (g s) y
  uniformity : ∀ s : Fin m → ℝ, (∀ i, 0 < s i) → ‖g s‖ ≤ 2

end PathFindingLP.Centering


