-- Prove2me | Definitions.Def_OnlineConvexOpt_Approachability_IsProjection
-- name    : OnlineConvexOpt_Approachability_IsProjection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:50.506748+00:00
-- url     : https://prove2.me/theorems/a10ca650-b9b2-4741-afde-6f7caea1b98e
-- title:
--   Euclidean projection $\Pi_{\mathcal K}$ onto a set
-- statement:
--   For $\mathcal K\subseteq\mathbb R^d$ and $z\in\mathbb R^d$, a point $p$ is **the projection of $z$ onto $\mathcal K$**, written $p=\Pi_{\mathcal K}(z)$, if
--
--   $$
--   p\in\mathcal K\quad\text{and}\quad \|z-p\|\le\|z-q\|\ \text{ for all } q\in\mathcal K ,
--   $$
--
--   that is, $p$ is a closest point of $\mathcal K$ to $z$. It is the projection step of online gradient descent (Algorithm 8).
--
--   **Formalization Note** The projection is a predicate rather than a function, so no junk value appears. For nonempty closed convex $\mathcal K$ the closest point exists and is unique.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, Algorithm 8, p. 42 (PDF p. 64), and p. 43 (PDF p. 65)

import Mathlib

namespace OnlineConvexOpt.Approachability

/-- **Euclidean projection onto a set, as a predicate** (`Π_K` of Algorithm 8).
Hazan, *Introduction to Online Convex Optimization*, 2nd ed., arXiv:1909.05207v3, Algorithm 8,
p. 42: "x_{t+1} = Π_K(y_{t+1})", and p. 43: "the algorithm projects the point back to the convex
set, i.e. finds its closest point in the convex set."

`IsProjection K z p` says that `p ∈ K` and `p` is a closest point of `K` to `z`.

**Formalization Note.** A predicate instead of a function, so that no junk value appears. For a
nonempty closed convex `K ⊆ ℝ^d` the closest point exists and is unique, so `IsProjection K z p`
holds exactly for `p = Π_K(z)`. -/
def IsProjection {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (z p : EuclideanSpace ℝ (Fin d)) : Prop :=
  p ∈ K ∧ ∀ q ∈ K, ‖z - p‖ ≤ ‖z - q‖

end OnlineConvexOpt.Approachability


