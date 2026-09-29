-- Prove2me | Definitions.Def_ConvexOptimization_IsBacktrackingStep
-- name    : ConvexOptimization_IsBacktrackingStep
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T15:25:28.545241+00:00
-- url     : https://prove2.me/theorems/baf57b24-ae0c-4ea3-931e-2ab770e0e18e
-- title:
--   Backtracking line search step
-- statement:
--   The step size produced by a **backtracking line search**, described by the property that characterizes its output rather than by the loop that computes it.
--
--   Fix a dimension $n$, a function $f : \mathbb{R}^n \to \mathbb{R}$, a field $g : \mathbb{R}^n \to \mathbb{R}^n$ playing the role of its gradient, and parameters $\alpha \in (0, 1/2)$, $\beta \in (0,1)$. Given a point $x$ and a search direction $\Delta$, a real number $t$ is a backtracking step when
--
--   $$t = \beta^{j} \text{ for some } j \in \mathbb{N}, \qquad f(x + t\Delta) \le f(x) + \alpha t \langle g(x), \Delta\rangle, \qquad \text{and} \qquad t = 1 \ \text{ or } \ f\bigl(x + \tfrac{t}{\beta}\Delta\bigr) > f(x) + \alpha \tfrac{t}{\beta} \langle g(x), \Delta\rangle .$$
--
--   The middle condition is the Armijo sufficient-decrease condition: the achieved decrease is at least the fraction $\alpha$ of the decrease predicted by the linear model. The last condition is maximality — either no backtracking happened at all ($t = 1$), or the previous, larger candidate $t/\beta$ failed Armijo — so $t$ is exactly the first accepted value of the sequence $1, \beta, \beta^2, \dots$ that the algorithm of B&V §9.2 returns.
--
--   Stating the step size as a predicate rather than as a function means every theorem about backtracking quantifies over *all* admissible runs, so results hold for any implementation and no choice function or termination proof is needed to state them.
--
--   **Formalization Note** Vectors live in `EuclideanSpace ℝ (Fin n)` and $\langle\cdot,\cdot\rangle$ is its real inner product. The gradient is supplied as an explicit field `g` rather than through a differentiability class; theorems that need it to be the true gradient add the hypothesis `∀ x, HasGradientAt f (g x) x`. The maximality clause is written as the negation of the Armijo inequality at $t/\beta$.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 464, §9.2 algorithm 9.2 (backtracking line search)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- Backtracking step size for direction `Δ` at `x` (B&V §9.2): the largest
`t = β^j` satisfying the Armijo condition `f(x + tΔ) ≤ f(x) + α t ⟪g x, Δ⟫`. -/
def IsBacktrackingStep {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  (∃ j : ℕ, t = β ^ j) ∧
  f (x + t • Δ) ≤ f x + α * t * ⟪g x, Δ⟫ ∧
  (t = 1 ∨ ¬ f (x + (t / β) • Δ) ≤ f x + α * (t / β) * ⟪g x, Δ⟫)

end ConvexOptimization


