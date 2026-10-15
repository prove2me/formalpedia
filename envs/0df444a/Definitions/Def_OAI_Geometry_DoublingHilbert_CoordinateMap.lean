-- Prove2me | Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateMap
-- name    : OAI_Geometry_DoublingHilbert_CoordinateMap
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:01:42.54793+00:00
-- url     : https://prove2.me/theorems/a1b0ca11-ddbc-4ba0-8111-f675bc97ae26
-- title:
--   The finite-rank coordinate map $z\mapsto\sum_{i\in I} z_i v_i$ from $\ell^2$ into a normed space
-- statement:
--   Let $B$ be a real normed space, let $I\subseteq\mathbb{N}$ be a finite set of coordinate indices, and let $v=(v_i)_{i\in I}$ be a family of vectors of $B$ indexed by the elements of $I$. The coordinate map attached to $(I,v)$ is the real-linear map $T_{I,v}:\ell^2\to B$ given by
--   $$
--   T_{I,v}(z)=\sum_{i\in I} z_i\,v_i\qquad\bigl(z=(z_0,z_1,z_2,\dots)\in\ell^2\bigr),
--   $$
--   where $\ell^2=\ell^2(\mathbb{N};\mathbb{R})$ and $z_i$ is the $i$-th coordinate of $z$. It reads off the coordinates of $z$ with index in $I$ and ignores all others; in particular it sends the unit vector $e_i$ to $v_i$ if $i\in I$ and to $0$ if $i\notin I$.
--
--   When the $v_i$ have norm at most $1$ and every coefficient of a linear combination of them is bounded by the norm of that combination (an Auerbach-type system), $T_{I,v}$ is the linear map used to place finite sets of points of $\ell^2$ that are supported in the coordinates $I$ inside an arbitrary infinite-dimensional normed space with bounded distortion.
--
--   **Formalization Note** The map is `coordinateMap I v : RealL2 →ₗ[ℝ] B`, with `v : I → B` indexed by the subtype of the finset `I`. It is bundled only as a linear map; continuity is not part of the definition (although the map has finite rank).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/CoordinateMap.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/CoordinateMap.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CompactBanach mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling
import Definitions.Def_OAI_Geometry_DoublingHilbert_CoordinateSupport

namespace OAI

open Set Metric
open scoped BigOperators
noncomputable section
namespace CompactBanach
open DoublingHilbert

noncomputable def coordinateMap {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (I : Finset ℕ) (v : I → B) : RealL2 →ₗ[ℝ] B where
  toFun z := ∑ i : I, z i • v i
  map_add' z w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [Finset.smul_sum, smul_smul]

end CompactBanach
end

end OAI


