-- Prove2me | Definitions.Def_GeomDRSub_IsDRSubmodular
-- name    : GeomDRSub_IsDRSubmodular
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:10.754803+00:00
-- url     : https://prove2.me/theorems/ef4fafb0-5f5f-4520-9975-8065c418cba6
-- title:
--   DR-submodular function (Definition 3.1)
-- statement:
--   A function $f:[0,1]^d\to\mathbb R$ is **DR-submodular** if it is continuously differentiable on the cube and its gradient is antitone in the coordinatewise order:
--   $$
--   u\le w\ \Longrightarrow\ \nabla f(u)\ge\nabla f(w)\qquad(u,w\in[0,1]^d),
--   $$
--   that is, $\partial_i f(w)\le\partial_i f(u)$ for every coordinate $i$ whenever $u_j\le w_j$ for all $j$. Gradients at boundary points are the continuous extensions of the interior gradients.
--
--   This is the differential form of diminishing returns; the objectives need not be monotone, so partial derivatives may have either sign.
--
--   **Formalization Note** Continuous differentiability on the cube is `ContDiffOn ℝ 1 f (cube d)` and the partial derivatives are taken within the cube. Nonnegativity of objectives is a separate hypothesis.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 3.1, p.8, Eq. (3)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_pd

namespace GeomDRSub

/-- **DR-submodularity (Definition 3.1).** Aggarwal–Lu, arXiv:2610.00545, p.8: "A continuously
differentiable function `f : Q → ℝ` is DR-submodular if `u ≤ w ⟹ ∇f(u) ≥ ∇f(w)` `(u, w ∈ Q)`. (3)
The gradients at the boundary are the continuous extensions of the interior gradients."

`IsDRSubmodular f` says that `f` is continuously differentiable on the cube and that for all `u, w`
in the cube with `u ≤ w` coordinatewise, every partial derivative satisfies `∂ᵢf(w) ≤ ∂ᵢf(u)`.

**Formalization Note.** "Continuously differentiable on `Q`" is `ContDiffOn ℝ 1 f (cube d)`, and
the partial derivatives are the within-cube derivatives `pd` (the boundary convention). The order
on vectors is coordinatewise (p.8). Nonnegativity of the objectives is a separate hypothesis of
each theorem. -/
def IsDRSubmodular {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ContDiffOn ℝ 1 f (cube d) ∧
    ∀ u ∈ cube d, ∀ w ∈ cube d, (∀ i, u i ≤ w i) → ∀ i, pd f i w ≤ pd f i u

end GeomDRSub


