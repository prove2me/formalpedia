-- Prove2me | Definitions.Def_BubeckCO_PSGD_IsSubgradient
-- name    : BubeckCO_PSGD_IsSubgradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:24:38.410159+00:00
-- url     : https://prove2.me/theorems/ee84621f-0488-49c8-b996-eb8624167be5
-- title:
--   Subgradient of a function on a set $X$ (Definition 1.2)
-- statement:
--   Let $X \subseteq \mathbb{R}^n$ and $f : X \to \mathbb{R}$, where $\mathbb{R}^n$ carries the Euclidean inner product. A vector $g \in \mathbb{R}^n$ is a **subgradient of $f$ at $x \in X$** if
--
--   $$
--   f(x) - f(y) \le g^\top (x - y) \qquad \text{for every } y \in X .
--   $$
--
--   The set of subgradients of $f$ at $x$ is denoted $\partial f(x)$. Equivalently, on $X$ the function $f$ lies above the affine function $y \mapsto f(x) + g^\top (y - x)$.
--
--   This is the notion of subgradient used throughout the monograph; the first-order oracle returns such a vector, and the projected subgradient descent method (3.2)–(3.3) steps along it.
--
--   **Formalization Note** The ambient space is `EuclideanSpace ℝ (Fin n)`. The book's $f : X \to \mathbb{R}$ is encoded as a function on all of $\mathbb{R}^n$ whose values off $X$ are never read. The subgradient is relative to $X$: the inequality is required only for $y \in X$, as in Definition 1.2, and the predicate includes $x \in X$.
-- source:
--   Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015, p. 235 (PDF p. 8), Definition 1.2 (Subgradients)

import Mathlib

namespace BubeckCO.PSGD

/-- **Subgradient of a function on a set (Definition 1.2).**
Bubeck, Convex Optimization: Algorithms and Complexity, Found. Trends Mach. Learn. 8(3-4), 2015,
p. 235 (PDF p. 8), Definition 1.2: "Let `X ⊂ ℝⁿ`, and `f : X → ℝ`. Then `g ∈ ℝⁿ` is a subgradient
of `f` at `x ∈ X` if for any `y ∈ X` one has `f(x) − f(y) ≤ gᵀ(x − y)`. The set of subgradients of
`f` at `x` is denoted `∂f(x)`."

`IsSubgradient X f x g` says that `x ∈ X` and `f x − f y ≤ ⟪g, x − y⟫` for every `y ∈ X`, i.e.
`g ∈ ∂f(x)` in the sense of Definition 1.2.

**Formalization Note.** `ℝⁿ` is `EuclideanSpace ℝ (Fin n)` and `gᵀ(x − y)` is the Euclidean inner
product. The function `f : X → ℝ` of the book is encoded as `f : ℝⁿ → ℝ` whose values off `X` are
never read. The subgradient is **relative to `X`**: the inequality is required only for `y ∈ X`,
exactly as in Definition 1.2 (this is not the global subgradient on `ℝⁿ`). -/
def IsSubgradient {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x g : EuclideanSpace ℝ (Fin n)) : Prop :=
  x ∈ X ∧ ∀ y ∈ X, f x - f y ≤ inner ℝ g (x - y)

end BubeckCO.PSGD


