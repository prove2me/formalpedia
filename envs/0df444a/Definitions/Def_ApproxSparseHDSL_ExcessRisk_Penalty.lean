-- Prove2me | Definitions.Def_ApproxSparseHDSL_ExcessRisk_Penalty
-- name    : ApproxSparseHDSL_ExcessRisk_Penalty
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:51:51.796856+00:00
-- url     : https://prove2.me/theorems/ab0e9f84-811c-4466-9043-9276bfdd8897
-- title:
--   (4), p. 3, and notation, p. 12 — the minimax concave penalty, the subdifferential of |·|, and the vector norms
-- statement:
--   This file fixes the penalty and the elementary notation used throughout the mission.
--
--   **Minimax concave penalty (MCP).** For tuning parameters $a, \lambda > 0$ and $\theta \ge 0$,
--
--   $$
--   P_\lambda(\theta) = \int_0^\theta \frac{[a\lambda - t]_+}{a}\,dt, \qquad [x]_+ := \max\{0, x\}.
--   $$
--
--   Equivalently $P_\lambda(\theta) = \lambda\theta - \theta^2/(2a)$ for $0 \le \theta \le a\lambda$ and $P_\lambda(\theta) = a\lambda^2/2$ for $\theta \ge a\lambda$. Its first and second derivatives $P_\lambda'$ and $P_\lambda''$ (used in the S³ONC) are the ordinary derivatives of this function; since the integrand is continuous, $P'_\lambda(\theta) = [a\lambda-\theta]_+/a$ everywhere and $P''_\lambda(\theta) = -1/a$ on $(0, a\lambda)$.
--
--   **Subdifferential of the absolute value.** $\partial|\cdot|(t) = [-1, 1]$ if $t = 0$ and $\{\operatorname{sign}(t)\}$ otherwise.
--
--   **Norms** (p. 12). For $v \in \mathbb R^m$: $\|v\| = (\sum_j v_j^2)^{1/2}$ is the Euclidean norm, $|v| = \sum_j |v_j|$ the $\ell_1$ norm, $\|v\|_\infty = \max_j |v_j|$ the max norm and $\|v\|_0$ the number of nonzero entries. The box $\{\beta : \|\beta\|_\infty \le R\}$ is written coordinatewise.
--
--   **Partial derivatives.** For $f : \mathbb R^p \to \mathbb R$, $\partial f/\partial\beta_j(\beta)$ is the derivative of $t \mapsto f(\beta_1, \dots, \beta_{j-1}, t, \beta_{j+1}, \dots, \beta_p)$ at $t = \beta_j$.
--
--   These objects are shared by every statement of the mission; the MCP is the folded concave penalty that regularizes the empirical risk in Problem (3).
--
--   **Formalization Note** The MCP is the literal interval integral (4), so $P'_\lambda$ and $P''_\lambda$ are Mathlib's `deriv` of it. Mathlib's norm on `Fin p → ℝ` is the sup norm, so the Euclidean norm is spelled out as `eucl`.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. 3, (4); p. 12, notation

import Mathlib

open MeasureTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- The minimax concave penalty (MCP), Liu–Ye–Lee (4), p. 3:
`P_λ(θ) = ∫₀^θ [aλ − t]₊ / a dt` with tuning parameters `a, λ > 0` (`lam` stands for `λ`).
It is written as the literal interval integral, so that `P′_λ` and `P″_λ` in Definition 1 are
`deriv (mcp a lam)` and `deriv (deriv (mcp a lam))`. -/
noncomputable def mcp (a lam θ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..θ, max (a * lam - t) 0 / a

/-- The subdifferential `∂|·|(t)` of the absolute value at `t ∈ ℝ`: `[-1, 1]` at `0`, and
`{sign t}` elsewhere. -/
noncomputable def absSubdiff (t : ℝ) : Set ℝ :=
  if t = 0 then Set.Icc (-1) 1 else {(SignType.sign t : ℝ)}

/-- `‖β‖₀`, the number of nonzero entries of `β` (p. 12). -/
noncomputable def l0 {p : ℕ} (β : Fin p → ℝ) : ℕ :=
  (Finset.univ.filter (fun j => β j ≠ 0)).card

/-- The Euclidean norm `‖v‖ = √(Σ v_j²)` (p. 12). Mathlib's norm on `ι → ℝ` is the sup norm,
so the Euclidean norm is spelled out. -/
noncomputable def eucl {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ j, v j ^ 2)

/-- The ℓ₁ norm `|v| = Σ |v_j|` (p. 12). -/
noncomputable def l1 {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ j, |v j|

/-- The max norm `‖v‖∞ = max_j |v_j|` (p. 12); equal to `0` on an empty index type. -/
noncomputable def supNorm {ι : Type} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ⨆ j, |v j|

/-- The box `{β : ‖β‖∞ ≤ R}`, written coordinatewise. -/
def InBox {p : ℕ} (R : ℝ) (β : Fin p → ℝ) : Prop :=
  ∀ j, |β j| ≤ R

/-- The `j`-th partial derivative `∂f/∂β_j` at `β`, as the derivative of the coordinate
section `t ↦ f(β₁, …, β_{j−1}, t, β_{j+1}, …, β_p)` at `t = β_j`. -/
noncomputable def partialJ {p : ℕ} (f : (Fin p → ℝ) → ℝ) (β : Fin p → ℝ) (j : Fin p) : ℝ :=
  deriv (fun t => f (Function.update β j t)) (β j)

end ApproxSparseHDSL.ExcessRisk


