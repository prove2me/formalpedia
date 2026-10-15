-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
-- name    : OAI_Geometry_ProjectionVolume_ProductVolumeGeneral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:04:14.805004+00:00
-- url     : https://prove2.me/theorems/af4872f0-176f-41e8-a31f-cf14c1121230
-- title:
--   Block splitting $\mathbb{R}^{r+s}\cong\mathbb{R}^r\times\mathbb{R}^s$ in general dimensions
-- statement:
--   For natural numbers $r$ and $s$, the file defines the block splitting map of Euclidean space
--
--   $$\beta_{r,s}:\mathbb{R}^{r+s}\to\mathbb{R}^r\times\mathbb{R}^s,\qquad \beta_{r,s}(x)=\bigl((x_1,\dots,x_r),\,(x_{r+1},\dots,x_{r+s})\bigr),$$
--
--   as a continuous linear isomorphism with continuous inverse, the inverse being concatenation of the two blocks.
--
--   It is the general-dimension version of the splitting $\mathbb{R}^{20}\cong\mathbb{R}^{10}\times\mathbb{R}^{10}$. The map carries Lebesgue measure on $\mathbb{R}^{r+s}$ to the product of the Lebesgue measures, so $\operatorname{vol}\bigl(\beta_{r,s}^{-1}(A\times B)\bigr)=\operatorname{vol}(A)\operatorname{vol}(B)$ for measurable $A\subseteq\mathbb{R}^r$ and $B\subseteq\mathbb{R}^s$. This is how the volume $1/(r!\,s!)$ of a product $T_r\times T_s$ of two standard simplices is obtained, and how the facets of such a product are given coordinates.
--
--   **Formalization Note** `splitEuclideanProduct r s : Euclidean (r + s) ≃L[ℝ] Euclidean r × Euclidean s` is built from the reindexing `finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)`. The target product carries Mathlib's sup norm, so the map is recorded as a continuous linear equivalence, not as an isometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductVolumeGeneral.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductVolumeGeneral.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Paper092

def splitEuclideanProduct (r s : ℕ) : Euclidean (r + s) ≃L[ℝ] Euclidean r × Euclidean s :=
  letI : ContinuousSMul ℝ (Euclidean r × Euclidean s) := Prod.continuousSMul
  let equiv : Euclidean (r + s) ≃ₗ[ℝ] Euclidean r × Euclidean s :=
    (((WithLp.linearEquiv 2 ℝ (Fin (r + s) → ℝ)).trans
      (LinearEquiv.piCongrLeft ℝ (fun _ : Fin (r + s) => ℝ)
        (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s))).symm).trans
      (LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℝ ℝ) |>.trans
      (LinearEquiv.prodCongr (WithLp.linearEquiv 2 ℝ (Fin r → ℝ)).symm
        (WithLp.linearEquiv 2 ℝ (Fin s → ℝ)).symm))
  equiv.toContinuousLinearEquiv

end Paper092

end

end OAI


