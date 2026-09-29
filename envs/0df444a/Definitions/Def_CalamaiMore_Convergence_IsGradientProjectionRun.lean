-- Prove2me | Definitions.Def_CalamaiMore_Convergence_IsGradientProjectionRun
-- name    : CalamaiMore_Convergence_IsGradientProjectionRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T12:29:31.430641+00:00
-- url     : https://prove2.me/theorems/c9bef87c-5b5f-4f80-96fc-e7eafa3fbc0a
-- title:
--   A run of the gradient projection method, conditions (2.1)–(2.3)
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, $P$ the projection into $\Omega$, and $f : E \to \mathbb R$. For $x \in \Omega$ write $x(\alpha) = P(x - \alpha \nabla f(x))$ for the **projected path**. Fix constants $\gamma_1, \gamma_2 > 0$ and $\mu_1, \mu_2 \in (0,1)$. A pair of sequences $(x_k)_{k \ge 0}$ in $E$ and $(\alpha_k)_{k\ge 0}$ in $\mathbb R$ is a **run of the gradient projection method** if $x_0 \in \Omega$ and, for every $k$:
--
--   1. $\alpha_k > 0$ and $x_{k+1} = x_k(\alpha_k) = P(x_k - \alpha_k \nabla f(x_k))$;
--   2. (sufficient decrease, (2.1))
--   $$
--   f(x_{k+1}) \le f(x_k) + \mu_1 \langle \nabla f(x_k), x_{k+1} - x_k \rangle;
--   $$
--   3. (steps not too small, (2.2)–(2.3)) either $\alpha_k \ge \gamma_1$, or there is $\bar\alpha_k$ with $\alpha_k \ge \gamma_2 \bar\alpha_k > 0$ and
--   $$
--   f(x_k(\bar\alpha_k)) > f(x_k) + \mu_2 \langle \nabla f(x_k), x_k(\bar\alpha_k) - x_k \rangle.
--   $$
--
--   This generalises the Armijo procedure (take $\gamma_1 = \gamma$, $\gamma_2 = \beta$, $\mu_1 = \mu_2 = \mu$) and does not require the steps $\alpha_k$ to be bounded.
--
--   **Formalization Note** The method is a predicate on the pair of sequences, indexed from $k = 0$, not a function: any step rule satisfying (2.1)–(2.3) is covered. Condition (2.3) is imposed on the witness $\bar\alpha_k$, not on $\alpha_k$. The ranges of $\gamma_1, \gamma_2, \mu_1, \mu_2$ are hypotheses of each theorem rather than part of the predicate; the paper's extra condition $\mu_1 \le \mu_2$, used only for the existence of a step, is not imposed.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 97, §2, conditions (2.1), (2.2), (2.3)

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_proj

namespace CalamaiMore.Convergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The projected path `x_k(α) = P(x_k - α ∇f(x_k))` of Calamai–Moré, p. 97. -/
noncomputable def projPath (f : E → ℝ) (Ω : Set E) (x : E) (α : ℝ) : E :=
  proj Ω (x - α • gradient f x)

/-- A run of the gradient projection method (2.1)–(2.3) of Calamai–Moré, p. 97, with constants
`γ₁ γ₂ μ₁ μ₂`: the iterates `x : ℕ → E` and steps `α : ℕ → ℝ` satisfy `x 0 ∈ Ω` and, for every
`k`,
* `α k > 0` and `x (k+1) = P(x k - α k ∇f(x k))`;
* (2.1) `f(x_{k+1}) ≤ f(x_k) + μ₁ ⟨∇f(x_k), x_{k+1} - x_k⟩`;
* (2.2) `α k ≥ γ₁`, or `α k ≥ γ₂ ᾱ > 0` for some `ᾱ` satisfying (2.3)
  `f(x_k(ᾱ)) > f(x_k) + μ₂ ⟨∇f(x_k), x_k(ᾱ) - x_k⟩`. -/
def IsGradientProjectionRun (f : E → ℝ) (Ω : Set E) (γ₁ γ₂ μ₁ μ₂ : ℝ)
    (x : ℕ → E) (α : ℕ → ℝ) : Prop :=
  x 0 ∈ Ω ∧
  ∀ k : ℕ,
    0 < α k ∧
    x (k + 1) = projPath f Ω (x k) (α k) ∧
    f (x (k + 1)) ≤ f (x k) + μ₁ * inner ℝ (gradient f (x k)) (x (k + 1) - x k) ∧
    (γ₁ ≤ α k ∨
      ∃ αbar : ℝ, 0 < γ₂ * αbar ∧ γ₂ * αbar ≤ α k ∧
        f (x k) + μ₂ * inner ℝ (gradient f (x k)) (projPath f Ω (x k) αbar - x k)
          < f (projPath f Ω (x k) αbar))

end CalamaiMore.Convergence


