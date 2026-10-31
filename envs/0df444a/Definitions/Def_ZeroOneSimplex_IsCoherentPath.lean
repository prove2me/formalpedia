-- Prove2me | Definitions.Def_ZeroOneSimplex_IsCoherentPath
-- name    : ZeroOneSimplex_IsCoherentPath
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:49:52.577909+00:00
-- url     : https://prove2.me/theorems/02264443-4b7c-4482-b060-f9ea180361b5
-- title:
--   Shadows, the upper path, and $c$-coherent monotone paths
-- statement:
--   For objectives $c,v\in\mathbb R^n$ the **shadow projection** is $\pi(x)=(v^\top x,\ c^\top x)\in\mathbb R^2$, and $\pi(Q)$ is the shadow of $Q$.
--
--   The **upper boundary** of a planar set $S$ consists of the points of $S$ that are highest among the points of $S$ with the same first coordinate. For the polygon $\pi(Q)$ it is the **upper path** from $u^0$ (the highest point of the leftmost face) to $u^1$ (the highest point of the rightmost face).
--
--   A $v$-monotone path $x^0,\dots,x^k$ in $Q$ is **$c$-coherent** if every $\pi(x^i)$ lies on the upper path and every vertex of $\pi(Q)$ on the upper path equals $\pi(x^i)$ for some $i$.
--
--   **Formalization Note** The paper defines the upper path with the line $L$ through $u^0$ and $u^1$; that line is undefined when $v^\top x$ is constant on $Q$, where the upper boundary is the top point of the vertical segment $\pi(Q)$. For a polygon the two descriptions agree.
-- source:
--   Black, De Loera, Kafer, Sanità, On the Simplex method for 0/1 polytopes, arXiv:2111.14050v1, §3.1, p.12 (shadow, upper path, c-coherent paths)

import Mathlib
import Definitions.Def_ZeroOneSimplex_IsEdge

set_option autoImplicit false

namespace ZeroOneSimplex

/-- The **shadow projection** `π(x) = (vᵀx, cᵀx)` (arXiv:2111.14050v1, p.12). -/
def shadowMap {n : ℕ} (c v : Fin n → ℝ) (x : Fin n → ℝ) : ℝ × ℝ :=
  (v ⬝ᵥ x, c ⬝ᵥ x)

/-- The **upper boundary** of a planar set `S`: the points of `S` that are highest (largest
second coordinate) among the points of `S` with the same first coordinate.

**Formalization Note.** For the polygon `S = π(Q)` this is the upper path of p.12, from
`u⁰` (the `e₂`-maximal vertex of the `e₁`-minimal face) to `u¹`: the paper describes it by the
line `L` through `u⁰` and `u¹`, which is undefined when `π(Q)` is a vertical segment (`vᵀx`
constant on `Q`); in that case the upper boundary is the top point. -/
def upperBoundary (S : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  {q | q ∈ S ∧ ∀ q' ∈ S, q'.1 = q.1 → q'.2 ≤ q.2}

/-- **`c`-coherent `v`-monotone path** (arXiv:2111.14050v1, p.12): a `v`-monotone path
`x 0, …, x k` in `Q` that `π` maps to the upper path of `π(Q)`: every `π(x i)` lies on the upper
path, and every vertex of `π(Q)` on the upper path is `π(x i)` for some `i ≤ k`. -/
def IsCoherentPath {n : ℕ} (Q : Set (Fin n → ℝ)) (c v : Fin n → ℝ) (x : ℕ → Fin n → ℝ)
    (k : ℕ) : Prop :=
  IsMonotonePath Q v x k ∧
    (∀ i ≤ k, shadowMap c v (x i) ∈ upperBoundary (shadowMap c v '' Q)) ∧
    ∀ q ∈ Set.extremePoints ℝ (shadowMap c v '' Q),
      q ∈ upperBoundary (shadowMap c v '' Q) → ∃ i ≤ k, shadowMap c v (x i) = q

end ZeroOneSimplex


