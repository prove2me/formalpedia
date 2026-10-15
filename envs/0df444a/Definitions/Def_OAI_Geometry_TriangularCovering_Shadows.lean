-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
-- name    : OAI_Geometry_TriangularCovering_Shadows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:39:50.819957+00:00
-- url     : https://prove2.me/theorems/529e0aad-5ac4-4047-8200-d2bb22bb6146
-- title:
--   Front faces of the tetrahedron for a viewing direction
-- statement:
--   Let $K\subset\mathbb{R}^3$ be the regular tetrahedron $\{(x,y,\sqrt2\,t):0\le t\le1,\ |x|\le1-t,\ |y|\le t\}$ with outward face normals $n_0=(\sqrt2,0,1)$, $n_1=(-\sqrt2,0,1)$, $n_2=(0,\sqrt2,-1)$, $n_3=(0,-\sqrt2,-1)$. For a vector $u\in\mathbb{R}^3$, the set of *front faces* is
--   $$
--   \mathrm{front}(u)=\{\,i\in\{0,1,2,3\}:\ \langle n_i,u\rangle>0\,\},
--   $$
--   the indices of the faces whose outward normal makes an acute angle with $u$. The file also contains the corresponding membership rule $i\in\mathrm{front}(u)\iff\langle n_i,u\rangle>0$.
--
--   For a unit vector $u$, the orthogonal shadow of $K$ on $u^\perp$ is the union of the projections of the front faces, and these projections overlap only along projected edges, which have zero area. This is how the shadow area of $K$ in direction $u$ is computed as a sum over $\mathrm{front}(u)$.
--
--   **Formalization Note** `front u` is the `Finset` filter of `Finset.univ : Finset (Fin 4)` by the condition `0 < inner ℝ (faceNormal i) u`, and `mem_front` is the simp lemma for membership.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Shadows.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Shadows.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def front (u : Space) : Finset (Fin 4) := Finset.univ.filter (fun i => 0 < inner ℝ (faceNormal i) u)

@[simp] lemma mem_front (u : Space) (i : Fin 4) : i ∈ front u ↔ 0 < inner ℝ (faceNormal i) u := by
  simp [front]

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI


