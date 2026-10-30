-- Prove2me | Definitions.Def_StochasticProg_RecourseKKT_subdifferential
-- name    : StochasticProg_RecourseKKT_subdifferential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:48:11.354481+00:00
-- url     : https://prove2.me/theorems/93a1827a-22bd-4031-a74b-2670388c2a04
-- title:
--   Subdifferential $\partial f(x)$ of an extended-real function
-- statement:
--   Let $f : \mathbb R^n \to [-\infty, +\infty]$ and $x \in \mathbb R^n$. A vector $\eta$ is a **subgradient** of $f$ at $x$ when $f(x)$ is finite and
--
--   $$
--   f(w) \ge f(x) + \eta^{\mathsf T} (w - x) \qquad \text{for all } w \in \mathbb R^n .
--   $$
--
--   The **subdifferential** $\partial f(x)$ is the set of subgradients at $x$. This is the notion in which the optimality condition (1.12) of Theorem 9 is stated, for $f = \mathcal Q$.
--
--   **Formalization Note** The book writes the inequality for real-valued $f$. For the functions used here, which take the value $+\infty$, the convex-analysis convention is used: $\partial f(x) = \emptyset$ where $f(x) = \pm\infty$, and points $w$ with $f(w) = +\infty$ impose no constraint.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, doi:10.1007/978-1-4614-0237-4, §2.11, printed p. 99 (PDF p. 125)

import Mathlib
open Matrix

namespace StochasticProg.RecourseKKT

/-- **Subgradients and the subdifferential `∂f(x)` of an extended-real function.**
Birge & Louveaux, *Introduction to Stochastic Programming*, 2nd ed., Springer 2011,
doi:10.1007/978-1-4614-0237-4, §2.11, printed p. 99 (PDF p. 125): "we express optimality in terms of subgradients at a
point x, or vectors, η, such that f(w) ≥ f(x) + ηᵀ(w − x) for all w. … The set of subgradients at a
point x is the subdifferential of f at x, written ∂f(x)."

For `f : ℜⁿ → [−∞, +∞]`, `η ∈ ∂f(x)` when `f(x)` is a real number `r` and
`f(w) ≥ r + ηᵀ(w − x)` for every `w ∈ ℜⁿ`.

**Formalization Note.** The book's functions here (`𝒬`, `cᵀx + 𝒬(x)`) take the value `+∞`. The
subgradient inequality is read with `f(x)` finite, the convex-analysis convention: `∂f(x) = ∅`
where `f(x) = ±∞`. Points `w` with `f(w) = +∞` impose no constraint. -/
def subdifferential {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {η | ∃ r : ℝ, f x = r ∧ ∀ w : Fin n → ℝ, ((r + η ⬝ᵥ (w - x) : ℝ) : EReal) ≤ f w}

end StochasticProg.RecourseKKT


