-- Prove2me | Definitions.Def_ShorNonsmooth_Subdiff_Subdifferential
-- name    : ShorNonsmooth_Subdiff_Subdifferential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T15:07:32.835427+00:00
-- url     : https://prove2.me/theorems/3f41475b-db7b-428a-add8-417ac89c0f91
-- title:
--   Subgradient and subdifferential $G_f(x_0)$ of a function relative to a domain $M$
-- statement:
--   Let $M \subseteq E_n$ be a set, $f : E_n \to \mathbb{R}$ a function (only its values on $M$ matter), and $x_0 \in E_n$. A vector $g \in E_n$ is a **subgradient** (or **generalized gradient**) of $f$ at $x_0$ relative to $M$ if
--
--   $$
--   f(x) - f(x_0) \ge (g,\, x - x_0) \qquad \text{for all } x \in M,
--   $$
--
--   where $(\cdot,\cdot)$ is the Euclidean inner product. The **subdifferential** $G(x_0) = G_f(x_0)$ is the set of all such subgradients.
--
--   This is the basic object of the whole book: subgradient methods replace the gradient by an arbitrary element of $G_f(x_0)$.
--
--   **Formalization Note** The book defines subgradients only for a convex $f$ with domain $M$ and $x_0$ an interior point of $M$; the definition here is stated for any $f$, $M$, $x_0$, and those assumptions appear as hypotheses of every theorem that uses it. $E_n$ is `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 9, inequality (1.3) and Definition

import Mathlib

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 9, inequality (1.3) and the Definition following it: a vector `g` is a
**subgradient** (generalized gradient) of `f` at `x₀` relative to the domain `M` if
`f x - f x₀ ≥ (g, x - x₀)` for every `x ∈ M`. The book uses this notion for a convex `f` with
domain `M` and `x₀` an interior point of `M`; those assumptions are hypotheses of the theorems. -/
def IsSubgradient {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ g : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ M, f x - f x₀ ≥ inner ℝ g (x - x₀)

/-- Shor (1985), p. 9: the **subdifferential** `G(x₀) = G_f(x₀)`, the set of all subgradients of
`f` at `x₀` relative to the domain `M`. -/
def subdifferential {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {g | IsSubgradient M f x₀ g}

end ShorNonsmooth.Subdiff


