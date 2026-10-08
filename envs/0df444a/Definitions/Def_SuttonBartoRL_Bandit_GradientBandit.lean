-- Prove2me | Definitions.Def_SuttonBartoRL_Bandit_GradientBandit
-- name    : SuttonBartoRL_Bandit_GradientBandit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:28:31.186975+00:00
-- url     : https://prove2.me/theorems/e5b647e0-75d4-4483-9ec4-8ff766b35844
-- title:
--   Soft-max action probabilities (2.11), expected reward and the gradient bandit update (2.12)
-- statement:
--   Consider a $k$-armed bandit with actions $1, \dots, k$ and a vector of numerical **action preferences** $H = (H(1), \dots, H(k)) \in \mathbb R^k$. The **soft-max** (Gibbs, Boltzmann) distribution selects action $a$ with probability
--
--   $$
--   \pi(a) = \frac{e^{H(a)}}{\sum_{b=1}^{k} e^{H(b)}}.
--   $$
--
--   If $q_*(x)$ is the true mean reward of action $x$, the **expected reward** under preferences $H$ is $\mathbb E[R] = \sum_x \pi(x)\, q_*(x)$, viewed as a function of $H$.
--
--   The **gradient bandit algorithm** with step size $\alpha > 0$ updates the preferences after selecting action $A$, receiving reward $R$ and comparing it with a baseline $\bar R$:
--
--   $$
--   H'(A) = H(A) + \alpha\,(R - \bar R)\,(1 - \pi(A)), \qquad H'(a) = H(a) - \alpha\,(R - \bar R)\,\pi(a) \quad \text{for all } a \ne A.
--   $$
--
--   Finally, for $f : \mathbb R^k \to \mathbb R$, the **partial derivative** $\partial f / \partial H(a)$ at $H$ is the derivative at $h = H(a)$ of the one-variable function obtained by replacing the $a$-th coordinate of $H$ by $h$.
--
--   These objects are the whole of §2.8: the policy (2.11), the update (2.12) and the performance measure whose gradient the box on pp. 38–40 computes.
--
--   **Formalization Note** Actions are `Fin k` (indices $0, \dots, k-1$ in Lean for the book's $1, \dots, k$). Every statement quantifies over some action $a$, so $k \ge 1$ whenever it has content, and the denominator $\sum_b e^{H(b)}$ is then positive. The partial derivative is Mathlib's `deriv` along the coordinate line; `deriv` is $0$ at a non-differentiable point, but all functions to which it is applied here (built from the soft-max) are differentiable.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, Eqs. (2.11)–(2.12), p. 37; expected reward E[R_t] = Σ_x π_t(x) q_*(x) and partial derivative, box "The Bandit Gradient Algorithm as Stochastic Gradient Ascent", p. 38

import Mathlib

namespace SuttonBartoRL.Bandit

/-- The soft-max (Gibbs/Boltzmann) action probabilities of Eq. (2.11):
`π(a) = e^{H(a)} / Σ_{b=1}^k e^{H(b)}` for a vector of action preferences `H : Fin k → ℝ`. -/
noncomputable def softmaxPolicy {k : ℕ} (H : Fin k → ℝ) (a : Fin k) : ℝ :=
  Real.exp (H a) / ∑ b, Real.exp (H b)

/-- The expected reward `E[R_t] = Σ_x π_t(x) q_*(x)` (p. 38) as a function of the preference
vector `H`, for true action values `qstar`. -/
noncomputable def expectedReward {k : ℕ} (qstar : Fin k → ℝ) (H : Fin k → ℝ) : ℝ :=
  ∑ x, softmaxPolicy H x * qstar x

/-- One step of the gradient bandit algorithm, Eq. (2.12): with preferences `H`, selected action
`A`, reward `R`, baseline `Rbar` and step size `α`, the new preference of action `a` is
`H(A) + α (R - Rbar)(1 - π(A))` if `a = A` and `H(a) - α (R - Rbar) π(a)` otherwise. -/
noncomputable def gradientBanditUpdate {k : ℕ} (α : ℝ) (H : Fin k → ℝ) (A : Fin k) (R Rbar : ℝ)
    (a : Fin k) : ℝ :=
  if a = A then H a + α * (R - Rbar) * (1 - softmaxPolicy H A)
  else H a - α * (R - Rbar) * softmaxPolicy H a

/-- The partial derivative `∂f/∂H(a)` of `f : ℝ^k → ℝ` at `H` in the coordinate `a`: the derivative
of `h ↦ f(H with H(a) replaced by h)` at `h = H(a)`. -/
noncomputable def partialDeriv {k : ℕ} (f : (Fin k → ℝ) → ℝ) (H : Fin k → ℝ) (a : Fin k) : ℝ :=
  deriv (fun h => f (Function.update H a h)) (H a)

end SuttonBartoRL.Bandit


