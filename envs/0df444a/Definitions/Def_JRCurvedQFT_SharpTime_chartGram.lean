-- Prove2me | Definitions.Def_JRCurvedQFT_SharpTime_chartGram
-- name    : JRCurvedQFT_SharpTime_chartGram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:35:42.992582+00:00
-- url     : https://prove2.me/theorems/1c55420e-459f-48b9-b1f2-80b739072b15
-- title:
--   Gram matrix $g_{ab}$ of the metric in a chart
-- statement:
--   For a point $p\in M$ and a coordinate point $x$ of the chart of $M$ at $p$, the **Gram matrix** is
--   $$g_{ab}(x)=\langle\partial_a,\partial_b\rangle_g,\qquad a,b=1,\dots,d,$$
--   where $\partial_a$ is the coordinate vector field of the chart at the point with coordinates $x$. Its determinant is the $\mathcal G=\det(g_{ab})$ of (4.2).
--
--   This is the coordinate expression of the metric used for the Riemannian volume and the Laplace–Beltrami operator.
-- source:
--   Jaffe, Ritter, Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral, arXiv:hep-th/0609003v1, §1, p. 3; Eqs. (4.1)–(4.2), p. 21

import Mathlib

open scoped Manifold ContDiff ENNReal Topology
open Bundle MeasureTheory

namespace JRCurvedQFT.SharpTime

variable {d : ℕ} {M : Type} [EMetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) x)]

/-- The Gram matrix `g_ab(x)` of the Riemannian metric in the chart of `M` at `p`.

Jaffe, Ritter, *Quantum Field Theory on Curved Backgrounds. I. The Euclidean Functional Integral*, arXiv:hep-th/0609003v1, §1 (p. 3, the Riemannian volume `dvol`) and (4.1)–(4.2), p. 21 (`g_ab`, `𝒢 = det(g_ab)`).

`chartGram p x i j = ⟨∂_i, ∂_j⟩_g` at the point `q = (chart at p)⁻¹(x)`, where `∂_i` is the image
of the `i`-th standard basis vector under the derivative of the inverse chart.

**Formalization Note** Points `x` outside the chart target give an unspecified value; the
matrix is only used on the chart target. -/
noncomputable def chartGram (p : M) (x : EuclideanSpace ℝ (Fin d)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => inner ℝ
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p).symm x (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
      (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) p).symm x (EuclideanSpace.single j 1))

end JRCurvedQFT.SharpTime


