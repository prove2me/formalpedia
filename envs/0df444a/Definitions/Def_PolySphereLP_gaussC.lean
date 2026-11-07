-- Prove2me | Definitions.Def_PolySphereLP_gaussC
-- name    : PolySphereLP_gaussC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:39.587188+00:00
-- url     : https://prove2.me/theorems/989cfd4c-e08d-4b9c-8670-20b8cb5136c5
-- title:
--   The standard circular complex Gaussian vector on $\mathbb C^m$
-- statement:
--   A **standard circular complex Gaussian vector** $\mathbf Z\in\mathbb C^m$ has independent coordinates $(G_j+iG'_j)/\sqrt2$, where all $G_j,G'_j$ are independent standard real Gaussians; thus $\mathbb E|Z_j|^2=1$ and $\mathbb E[Z_j^2]=0$.
--
--   **Formalization Note** The product of $m$ copies of the published law `BraneBrauer.Orthogonal.complexGaussian` (independent real and imaginary parts, each $N(0,1/2)$). The module also records that this law is a probability measure.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), p.13

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_ComplexGaussian

namespace PolySphereLP

/-- The published circular complex Gaussian law is a probability measure (pushforward of a product
of two Gaussian probability measures under a continuous map). -/
instance complexGaussian_isProbability :
    MeasureTheory.IsProbabilityMeasure BraneBrauer.Orthogonal.complexGaussian := by
  unfold BraneBrauer.Orthogonal.complexGaussian
  exact MeasureTheory.Measure.isProbabilityMeasure_map (by fun_prop)

/-- **The standard circular complex Gaussian vector `Z ∈ ℂ^m`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), p.13: "A standard circular
complex Gaussian vector `Z ∈ ℂ^m` has independent coordinates `(G_j + iG'_j)/√2`, where all
`G_j, G'_j` are independent standard real Gaussians."

`gaussC m` is the product of `m` copies of `BraneBrauer.Orthogonal.complexGaussian` (real and
imaginary parts independent `N(0, 1/2)`), so `E|Z_j|² = 1`. -/
noncomputable def gaussC (m : ℕ) : MeasureTheory.Measure (Fin m → ℂ) :=
  MeasureTheory.Measure.pi (fun _ : Fin m => BraneBrauer.Orthogonal.complexGaussian)

end PolySphereLP


