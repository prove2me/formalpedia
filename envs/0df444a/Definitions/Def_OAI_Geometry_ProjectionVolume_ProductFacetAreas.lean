-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas
-- name    : OAI_Geometry_ProjectionVolume_ProductFacetAreas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:06:10.342604+00:00
-- url     : https://prove2.me/theorems/83cf7238-d9ea-41b6-91f9-03c13d13378c
-- title:
--   Isometric block splitting, block-diagonal linear maps and the product orthonormal basis of $\mathbb{R}^{r+s}$
-- statement:
--   Let $r,s,t,u\in\mathbb{N}$ and write $x=(x',x'')$ for the splitting of $x\in\mathbb{R}^{r+s}$ into its first $r$ and last $s$ coordinates. The file defines:
--
--   1. **Isometric splitting.** The linear isometric isomorphism $x\mapsto(x',x'')$ from $\mathbb{R}^{r+s}$ onto the product $\mathbb{R}^r\oplus_2\mathbb{R}^s$ equipped with the Euclidean norm $\|(a,b)\|=\sqrt{\|a\|^2+\|b\|^2}$.
--   2. **Block-diagonal map.** For linear maps $f:\mathbb{R}^r\to\mathbb{R}^t$ and $g:\mathbb{R}^s\to\mathbb{R}^u$, the linear map $$f\oplus g:\mathbb{R}^{r+s}\to\mathbb{R}^{t+u},\qquad (f\oplus g)(x)=\bigl(f(x'),\,g(x'')\bigr).$$
--   3. **Product orthonormal basis.** The orthonormal basis of $\mathbb{R}^{r+s}$ indexed by the disjoint union $\{1,\dots,r\}\sqcup\{1,\dots,s\}$, whose vectors are $(e_i,0)$ for $i\le r$ and $(0,e_j)$ for $j\le s$; it is obtained by transporting the product of the two standard bases through the isometric splitting.
--
--   In this basis the Gram matrix of $f\oplus g$ is block diagonal, so the Jacobian of $f\oplus g$ (the square root of its Gram determinant) is the product of the Jacobians of $f$ and $g$. Consequently, for measurable $A\subseteq\mathbb{R}^r$ and $B\subseteq\mathbb{R}^s$, the $(r+s)$-dimensional Hausdorff measure of $\{y\in\mathbb{R}^{t+u}:\ y'\in f(A),\ y''\in g(B)\}$, where $y'$ and $y''$ are the first $t$ and the last $u$ coordinates of $y$, equals $J(f)\,J(g)\operatorname{vol}(A)\operatorname{vol}(B)$. This computes the areas of the facets of a product of two simplices, each of which is a facet of one factor times the other factor.
--
--   **Formalization Note** The Lean names are `splitEuclideanProductL2 r s : Euclidean (r + s) ≃ₗᵢ[ℝ] WithLp 2 (Euclidean r × Euclidean s)`, `euclideanProductMap f g` (which conjugates `f.prodMap g` by the continuous linear splitting `splitEuclideanProduct`), and `productOrthonormalBasis r s : OrthonormalBasis (Fin r ⊕ Fin s) ℝ (Euclidean (r + s))`. The Jacobian is Mathlib's `LinearMap.normDet`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductFacetAreas.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductVolumeGeneral

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal Pointwise

namespace Paper092

def splitEuclideanProductL2 (r s : ℕ) :
    Euclidean (r + s) ≃ₗᵢ[ℝ] WithLp 2 (Euclidean r × Euclidean s) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSumFinEquiv : Fin r ⊕ Fin s ≃ Fin (r + s)).symm).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin r ⊕ Fin s => ℝ))

def euclideanProductMap {r s t u : ℕ} (f : Euclidean r →ₗ[ℝ] Euclidean t)
    (g : Euclidean s →ₗ[ℝ] Euclidean u) :
    Euclidean (r + s) →ₗ[ℝ] Euclidean (t + u) :=
  (splitEuclideanProduct t u).symm.toLinearMap.comp
    ((f.prodMap g).comp (splitEuclideanProduct r s).toLinearMap)

def productOrthonormalBasis (r s : ℕ) :
    OrthonormalBasis (Fin r ⊕ Fin s) ℝ (Euclidean (r + s)) :=
  ((EuclideanSpace.basisFun (Fin r) ℝ).prod (EuclideanSpace.basisFun (Fin s) ℝ)).map
    (splitEuclideanProductL2 r s).symm

end Paper092

end

end OAI


