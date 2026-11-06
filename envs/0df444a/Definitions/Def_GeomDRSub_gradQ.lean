-- Prove2me | Definitions.Def_GeomDRSub_gradQ
-- name    : GeomDRSub_gradQ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:00.760027+00:00
-- url     : https://prove2.me/theorems/df043799-06a8-4f54-b429-070e173eb1a4
-- title:
--   Gradient $\nabla f$ on the closed cube
-- statement:
--   For $f:\mathbb R^d\to\mathbb R$ and $y$ in the cube, $\nabla f(y)\in\mathbb R^d$ is the vector with coordinates $\partial_i f(y)$, $i\in[d]$, where $\partial_i f$ is the partial derivative within the cube (with the boundary convention of Definition 3.1).
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 3.1, p.8, Definition 3.1

import Mathlib
import Definitions.Def_GeomDRSub_pd

namespace GeomDRSub

/-- **The gradient `∇f(y)` on the closed cube.** Aggarwal–Lu, arXiv:2610.00545, Section 3.1, p.8:
the vector with coordinates `∂ᵢf(y)`, `i ∈ [d]`, with the boundary convention of Definition 3.1
(see `pd`). -/
noncomputable def gradQ {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => pd f i y)

end GeomDRSub


