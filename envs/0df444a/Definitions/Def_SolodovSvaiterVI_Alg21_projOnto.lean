-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_projOnto
-- name    : SolodovSvaiterVI_Alg21_projOnto
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:46:45.576253+00:00
-- url     : https://prove2.me/theorems/aa2a66e8-f896-414b-909f-2661dc453c28
-- title:
--   Euclidean projection $P_K[x]$ onto a set $K \subseteq \mathbb{R}^n$
-- statement:
--   Let $K \subseteq \mathbb{R}^n$ and $x \in \mathbb{R}^n$, where $\mathbb{R}^n$ carries the Euclidean norm $\|\cdot\|$. The **projection** of $x$ onto $K$ is the nearest point of $K$ to $x$:
--
--   $$P_K[x] := \arg\min_{y \in K} \|y - x\|.$$
--
--   When $K$ is nonempty, closed and convex, the minimizer exists and is unique, so $P_K[x]$ is a well-defined point of $K$. The projection is the basic operation of every method in this mission: the residual, the halfspaces $H_i$ and the update of Algorithm 2.1 are all built from it.
--
--   **Formalization Note** $\mathbb{R}^n$ is `EuclideanSpace ℝ (Fin n)`. `projOnto K x` is defined as a point $p \in K$ with $\|x - p\| \le \|x - y\|$ for all $y \in K$ (chosen by `Classical.choose`) whenever such a point exists, and as the junk value $x$ otherwise (for instance when $K = \emptyset$). On nonempty closed convex sets the nearest point exists and is unique, so `projOnto K x` coincides with $P_K[x]$ there; the paper only projects onto such sets ($C$, the halfspaces $H_i$, and $C \cap H_i$), so the junk branch is never reached under the hypotheses of the theorems.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 766, definition of the projection operator P_C

import Mathlib

namespace SolodovSvaiterVI.Alg21

/-- The Euclidean projection `P_K[x] := arg min_{y ∈ K} ‖y − x‖` onto a set `K ⊆ ℝⁿ`
(Solodov–Svaiter, SIAM J. Control Optim. 37 (1999), p. 766).

If some point `p ∈ K` is nearest to `x` among all points of `K`, `projOnto K x` is such a point
(chosen by `Classical.choose`); for a nonempty closed convex `K` the nearest point exists and is
unique, so `projOnto K x` is exactly `P_K[x]`.

**Formalization Note.** When no nearest point exists (e.g. `K = ∅`) the value is the junk value
`x`. The paper only projects onto nonempty closed convex sets (`C`, the halfspaces `Hᵢ`, and
`C ∩ Hᵢ`), where the junk branch is never reached. -/
noncomputable def projOnto {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  open Classical in
  if h : ∃ p ∈ K, ∀ y ∈ K, ‖x - p‖ ≤ ‖x - y‖ then Classical.choose h else x

end SolodovSvaiterVI.Alg21


