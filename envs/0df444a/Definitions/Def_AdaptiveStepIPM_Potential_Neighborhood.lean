-- Prove2me | Definitions.Def_AdaptiveStepIPM_Potential_Neighborhood
-- name    : AdaptiveStepIPM_Potential_Neighborhood
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:56.625995+00:00
-- url     : https://prove2.me/theorems/85a681de-8c28-4524-87d3-6db28f75ebcc
-- title:
--   The duality measure $\mu = x^Ts/n$, $\|z\|_\infty^-$ and the neighbourhood $\mathcal N_\infty^-(\beta)$
-- statement:
--   For the standard-form linear program and strictly feasible set $\mathcal F^0$ defined in the preceding item, let $n \ge 1$. The **duality measure** of a pair is $\mu = x^Ts/n$.
--
--   For $z \in \mathbb R^n$ let $(z^-)_j := \min\{z_j, 0\}$ and $\|z\|_\infty^- := \|z^-\|_\infty$, where $\|\cdot\|_\infty$ is the usual $\ell_\infty$ norm. This is not a norm, but it obeys the triangle inequality. For $\beta \in (0,1)$ the **neighbourhood** of the central path is
--   $$
--   \mathcal N_\infty^-(\beta) = \bigl\{(x,s) \in \mathcal F^0 : \|Xs - \mu e\|_\infty^- \le \beta\mu\bigr\},
--   $$
--   where $X = \mathrm{diag}(x)$ and $e$ is the all-ones vector. Equivalently, $x_j s_j \ge (1-\beta)\mu$ for every $j$.
--
--   These are the objects on which the adaptive-step and potential-reduction algorithms of Mizuno, Todd and Ye move: every iterate stays in $\mathcal N_\infty^-(\beta)$, a wide neighbourhood that fills almost all of $\mathcal F^0$ as $\beta \to 1$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ`; the paper's index $j = 1,\dots,n$ is `j : Fin n`. $\|\cdot\|_\infty$ is Mathlib's sup norm on `Fin n → ℝ`. $\mu$ divides by $n$ and is meaningful only for $n \ge 1$, which every theorem using it assumes. `centralityResidual x s` is the vector $Xs - \mu e$.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 2, μ and N∞⁻(β)

import Mathlib
import Definitions.Def_AdaptiveStepIPM_Potential_StandardLP
import Definitions.Def_AdaptiveStepIPM_PredCorr_Neighborhoods

/-!
Mizuno, Todd, Ye, *On adaptive-step primal-dual interior-point algorithms for linear
programming*, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), §1, pp. 1–2.

Given the standard-form pair and `F⁰` in `StandardLP`, the duality measure `μ = xᵀs/n`, the one-sided seminorm
`‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j := min{z_j, 0}`, and the neighbourhood
`N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}`.

Indices: the paper's `j = 1, …, n` is `j : Fin n` (`j ↦ j − 1`).
-/

open Matrix

namespace AdaptiveStepIPM.Potential

/-- `‖z‖⁻_∞ := ‖z⁻‖_∞` with `(z⁻)_j = min{z_j, 0}` (p. 2). The norm on `Fin n → ℝ` is
Mathlib's sup norm, i.e. the `ℓ_∞` norm `max_j |·|` (and `0` when `n = 0`). -/
noncomputable def negInfNorm {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  ‖fun j => min (z j) 0‖

/-- The vector `Xs − μe`, with components `x_j s_j − μ`. -/
noncomputable def centralityResidual {n : ℕ} (x s : Fin n → ℝ) : Fin n → ℝ :=
  fun j => x j * s j - AdaptiveStepIPM.PredCorr.mu x s

/-- The neighbourhood `N_∞⁻(β) = {(x, s) ∈ F⁰ : ‖Xs − μe‖⁻_∞ ≤ βμ}` (p. 2). -/
def InNinfMinus {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (β : ℝ) (x s : Fin n → ℝ) : Prop :=
  (⟨A, b, c⟩ : StandardLP m n).StrictlyFeasible x s ∧
    negInfNorm (centralityResidual x s) ≤ β * AdaptiveStepIPM.PredCorr.mu x s

end AdaptiveStepIPM.Potential


