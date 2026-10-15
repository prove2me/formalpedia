-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_ProductNormals
-- name    : OAI_Geometry_ProjectionVolume_ProductNormals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:58:18.224889+00:00
-- url     : https://prove2.me/theorems/26ee2ccb-5bd5-4f1e-8a42-d19ba847cb22
-- title:
--   The two block inclusions $\mathbb{R}^{10}\to\mathbb{R}^{20}$, $y\mapsto(y,0)$ and $y\mapsto(0,y)$
-- statement:
--   Identify $\mathbb{R}^{20}$ with $\mathbb{R}^{10}\times\mathbb{R}^{10}$ by splitting a point $x$ into its first ten coordinates $x'$ and its last ten coordinates $x''$. The file defines the two block inclusions
--
--   $$\iota_1(y)=(y,0),\qquad \iota_2(y)=(0,y)\qquad(y\in\mathbb{R}^{10}),$$
--
--   that is, $\iota_1(y)=(y_1,\dots,y_{10},0,\dots,0)$ and $\iota_2(y)=(0,\dots,0,y_1,\dots,y_{10})$.
--
--   Both maps preserve norms, and $\langle x,\iota_1(y)\rangle=\langle x',y\rangle$, $\langle x,\iota_2(y)\rangle=\langle x'',y\rangle$ for every $x\in\mathbb{R}^{20}$. They lift the facet normals of the standard simplex $T_{10}$ (the coordinate vectors $e_i$ and the diagonal unit normal $\mathbf 1/\sqrt{10}$) to unit normals of the $22$ facets of the product $T_{10}\times T_{10}$, which is how the area-scaling factors in the brightness function of the product are obtained.
--
--   **Formalization Note** The Lean names are `liftFirst` and `liftSecond`, defined as `splitBlocks.symm (x, 0)` and `splitBlocks.symm (0, x)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/ProductNormals.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/ProductNormals.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals

namespace OAI

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Paper092

def liftFirst (x : Euclidean 10) : Euclidean 20 := splitBlocks.symm (x, 0)
def liftSecond (x : Euclidean 10) : Euclidean 20 := splitBlocks.symm (0, x)

end Paper092

end

end OAI


