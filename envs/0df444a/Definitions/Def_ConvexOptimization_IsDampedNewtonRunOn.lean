-- Prove2me | Definitions.Def_ConvexOptimization_IsDampedNewtonRunOn
-- name    : ConvexOptimization_IsDampedNewtonRunOn
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-17T01:41:56.904094+00:00
-- url     : https://prove2.me/theorems/99095104-57f7-459f-9fed-f1ef21c4b40a
-- title:
--   Domain-confined backtracking line search and damped Newton run
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 464-465, §9.2 (backtracking line search) and pp. 487-488, §9.5.2 (damped Newton), read with the book's standing convention (p. 457, §9.1) that an objective takes the value $+\infty$ off its domain.

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Domain-confined backtracking line search** (B&V §9.2, read with the book's standing
convention that an objective is `+∞` off its domain).

`t` is the largest step of the form `β ^ j` for which the trial point `x + t • Δ` is still
in `Ω` *and* satisfies the Armijo condition.  Trial points outside `Ω` are rejected
outright — which is exactly what happens in B&V, where `f` takes the value `+∞` there, so
that the Armijo inequality cannot hold.  For a real-valued `f` this has to be said
explicitly: nothing constrains `f` off `Ω`, and `logBarrier` in particular takes finite
junk values there. -/
def IsBacktrackingStepOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ) : Prop :=
  (∃ j : ℕ, t = β ^ j) ∧
  (x + t • Δ ∈ Ω ∧ f (x + t • Δ) ≤ f x + α * t * ⟪g x, Δ⟫) ∧
  (t = 1 ∨ ¬ (x + (t / β) • Δ ∈ Ω ∧
    f (x + (t / β) • Δ) ≤ f x + α * (t / β) * ⟪g x, Δ⟫))

/-- A damped-Newton run confined to `Ω`, using the domain-confined line search
`IsBacktrackingStepOn`.  Every iterate lies in `Ω`, the search direction solves the Newton
system, and the step size comes from the line search. -/
def IsDampedNewtonRunOn {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, x k ∈ Ω ∧ ∃ (Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ),
    H (x k) Δ = -g (x k) ∧ IsBacktrackingStepOn Ω f g α β (x k) Δ t ∧
    x (k + 1) = x k + t • Δ

end ConvexOptimization


