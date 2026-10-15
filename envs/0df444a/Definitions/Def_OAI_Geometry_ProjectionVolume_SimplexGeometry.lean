-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
-- name    : OAI_Geometry_ProjectionVolume_SimplexGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:53:55.495101+00:00
-- url     : https://prove2.me/theorems/bb0d3afa-41b9-484b-96ed-69a7586d54a3
-- title:
--   The block splitting map $\mathbb{R}^{20}\to\mathbb{R}^{10}\times\mathbb{R}^{10}$
-- statement:
--   Write a point of Euclidean space $\mathbb{R}^{20}$ as $x=(x_1,\dots,x_{20})$, and let $x'=(x_1,\dots,x_{10})$ and $x''=(x_{11},\dots,x_{20})$ be its first and second block of ten coordinates. The file defines the block splitting map
--
--   $$\beta:\mathbb{R}^{20}\to\mathbb{R}^{10}\times\mathbb{R}^{10},\qquad \beta(x)=(x',x''),$$
--
--   as a continuous linear isomorphism of real vector spaces; its inverse $\beta^{-1}(a,b)$ is the concatenation of $a$ and $b$.
--
--   The product body $K=T_{10}\times T_{10}$, where $T_{10}=\operatorname{conv}\{0,e_1,\dots,e_{10}\}\subset\mathbb{R}^{10}$ is the standard simplex, is the preimage $\beta^{-1}(T_{10}\times T_{10})$. Through $\beta$, compactness, convexity and interior points, Lebesgue measure (the map is volume preserving) and inner products ($\langle x,y\rangle=\langle x',y'\rangle+\langle x'',y''\rangle$) are transferred between $\mathbb{R}^{20}$ and the product of two copies of $\mathbb{R}^{10}$. The product zonotope that turns out to be the projection body of $K$ is defined as a preimage under the same map.
--
--   **Formalization Note** `splitBlocks : Euclidean 20 ≃L[ℝ] Euclidean 10 × Euclidean 10` is assembled from the identification of `EuclideanSpace ℝ (Fin 20)` with `Fin 20 → ℝ`, the reindexing `finSumFinEquiv : Fin 10 ⊕ Fin 10 ≃ Fin 20`, the splitting of a function on a sum type into a pair, and re-wrapping both halves as Euclidean vectors. Its two components agree definitionally with `firstBlock` and `secondBlock`. The product type carries Mathlib's sup norm, so the map is recorded as a continuous linear equivalence rather than as an isometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Paper092

def splitBlocks : Euclidean 20 ≃L[ℝ] Euclidean 10 × Euclidean 10 :=
  (((WithLp.linearEquiv 2 ℝ (Fin 20 → ℝ)).trans
      (LinearEquiv.piCongrLeft ℝ (fun _ : Fin 20 => ℝ)
        (finSumFinEquiv : Fin 10 ⊕ Fin 10 ≃ Fin 20)).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin 10) (Fin 10) ℝ ℝ) |>.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin 10 → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Fin 10 → ℝ)).symm)).toContinuousLinearEquiv

end Paper092

end

end OAI


