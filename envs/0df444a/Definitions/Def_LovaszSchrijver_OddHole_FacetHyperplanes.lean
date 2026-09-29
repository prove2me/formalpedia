-- Prove2me | Definitions.Def_LovaszSchrijver_OddHole_FacetHyperplanes
-- name    : LovaszSchrijver_OddHole_FacetHyperplanes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:44:43.540425+00:00
-- url     : https://prove2.me/theorems/1b758bc7-4451-4f74-887a-08e963ae10db
-- title:
--   The hyperplanes Hᵢ = {xᵢ = 0} and Gᵢ = {xᵢ = x₀} (Section 1.b)
-- statement:
--   For $1 \le i \le n$, Lovász and Schrijver define (p. 171) the hyperplanes of $\mathbb{R}^{n+1}$
--   $$H_i = \{x \in \mathbb{R}^{n+1} : x_i = 0\}, \qquad G_i = \{x \in \mathbb{R}^{n+1} : x_i = x_0\}.$$
--   They support the cone $Q$ at a facet, and all facets of $Q$ arise this way. They appear in Lemma 1.3, which bounds $N(K)$ by the Minkowski sum $(K \cap H_i) + (K \cap G_i)$.
--
--   **Formalization Note** Coordinates are indexed by `Option ι`, with `none` the coordinate $x_0$.
-- source:
--   Lovász and Schrijver, Cones of matrices and set-functions and 0–1 optimization, SIAM J. Optim. 1(2) (1991), p. 171, Section 1.b

import Mathlib

namespace LovaszSchrijver.OddHole

/-- The hyperplane `Hᵢ = {x ∈ ℝ^{n+1} : xᵢ = 0}` (p. 171). -/
def Hplane {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = 0}

/-- The hyperplane `Gᵢ = {x ∈ ℝ^{n+1} : xᵢ = x₀}` (p. 171). -/
def Gplane {ι : Type} (i : ι) : Set (Option ι → ℝ) :=
  {x | x (some i) = x none}

end LovaszSchrijver.OddHole


