-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
-- name    : OAI_Geometry_ProjectionVolume_ProjectionJacobian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:07:27.095719+00:00
-- url     : https://prove2.me/theorems/9fa1faa9-7368-42fd-9858-c2bd0bdb51b1
-- title:
--   Orthogonal projection from the hyperplane $v^\perp$ onto the hyperplane $u^\perp$
-- statement:
--   For vectors $u,v\in\mathbb{R}^n$ write $u^\perp=\{x\in\mathbb{R}^n:\ \langle u,x\rangle=0\}$ and let $P_{u^\perp}$ be the orthogonal projection of $\mathbb{R}^n$ onto $u^\perp$. The file defines the linear map
--
--   $$\Phi_{u,v}:v^\perp\to\mathbb{R}^n,\qquad \Phi_{u,v}(x)=P_{u^\perp}(x),$$
--
--   the restriction of $P_{u^\perp}$ to the hyperplane $v^\perp$, regarded as a map into the ambient space.
--
--   When $u$ is a unit vector, $P_{u^\perp}x=x-\langle u,x\rangle u$; when $u$ and $v$ are both unit vectors, the Jacobian of $\Phi_{u,v}$ (the square root of its Gram determinant) equals $|\langle u,v\rangle|$. Hence orthogonal projection onto $u^\perp$ multiplies $(n-1)$-dimensional areas of subsets of a hyperplane with unit normal $v$ by $|\langle u,v\rangle|$, and, for a unit vector $v$ and an arbitrary $u$, the brightness in direction $u$ of a set contained in an affine hyperplane $\{\langle v,x\rangle=c\}$ is $|\langle u,v\rangle|$ times its $(n-1)$-dimensional area. Summed over the visible facets of a polytope, this single-facet identity yields the brightness functions of the simplex and of the product of two simplices.
--
--   **Formalization Note** `hyperplaneProjection u v : normalHyperplane v →ₗ[ℝ] Euclidean n` is `(normalHyperplane u).starProjection` composed with the inclusion of the subspace `normalHyperplane v`, where `normalHyperplane u` is the orthogonal complement of the span of $u$. For $u=0$ this complement is the whole space, matching the formula for $u^\perp$ above; the Jacobian identity is stated only for unit vectors.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProjectionJacobian.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProjectionJacobian.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductFacetAreas

namespace OAI

universe uι

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

namespace Paper092

noncomputable def hyperplaneProjection {n : ℕ} (u v : Euclidean n) :
    normalHyperplane v →ₗ[ℝ] Euclidean n :=
  (normalHyperplane u).starProjection.toLinearMap.comp (normalHyperplane v).subtype

end Paper092

end OAI


