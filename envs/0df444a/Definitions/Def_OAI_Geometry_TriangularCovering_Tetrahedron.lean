-- Prove2me | Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
-- name    : OAI_Geometry_TriangularCovering_Tetrahedron
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:38:36.998141+00:00
-- url     : https://prove2.me/theorems/7efd8f3a-b0ff-49ce-8a66-fd785de0013e
-- title:
--   Face normals, supporting inequalities and faces of the tetrahedron $K$
-- statement:
--   Let $H=\sqrt2$ and $K=\{(x,y,Ht):\ 0\le t\le1,\ |x|\le1-t,\ |y|\le t\}\subset\mathbb{R}^3$, the regular tetrahedron with vertices $(\pm1,0,0)$ and $(0,\pm1,H)$. This file names its four faces.
--
--   1. **Face normals and bounds.** For $i=0,1,2,3$,
--   $$
--   n_0=(H,0,1),\quad n_1=(-H,0,1),\quad n_2=(0,H,-1),\quad n_3=(0,-H,-1),\qquad (c_0,c_1,c_2,c_3)=(H,H,0,0).
--   $$
--   For $z=(x,y,Ht)$ the inequalities $\langle n_i,z\rangle\le c_i$ read $x+t\le1$, $-x+t\le1$, $y\le t$ and $-y\le t$ respectively.
--   2. **Face vertices.** The ordered vertex triples are
--   $F_0$: $(1,0,0),(0,1,H),(0,-1,H)$; $F_1$: $(-1,0,0),(0,1,H),(0,-1,H)$; $F_2$: $(0,1,H),(1,0,0),(-1,0,0)$; $F_3$: $(0,-1,H),(1,0,0),(-1,0,0)$.
--   3. **Faces.** $F_i=\{z\in K:\ \langle n_i,z\rangle=c_i\}$.
--
--   The vectors $n_i$ are outward normals (not unit vectors; $\|n_i\|=\sqrt3$), and $K$ is the intersection of the four half-spaces $\langle n_i,z\rangle\le c_i$, with $F_i$ the triangle spanned by the listed vertex triple. These descriptions are used to compute the area of the orthogonal shadow of $K$ in every direction.
--
--   **Formalization Note** The Lean names are `faceNormal`, `faceBound`, `faceVertices` and `face`, indexed by `Fin 4`; the points are written `point x y t` $=(x,y,Ht)$. The half-space description of $K$ and the identification of each face with a triangle are proved as separate theorems.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularCovering mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

def faceNormal : Fin 4 → Space := ![!₂[H,0,1], !₂[-H,0,1], !₂[0,H,-1], !₂[0,-H,-1] ]
def faceBound : Fin 4 → ℝ := ![H,H,0,0]
def faceVertices : Fin 4 → Fin 3 → Space
  | 0 => ![point 1 0 0, point 0 1 1, point 0 (-1) 1]
  | 1 => ![point (-1) 0 0, point 0 1 1, point 0 (-1) 1]
  | 2 => ![point 0 1 1, point 1 0 0, point (-1) 0 0]
  | 3 => ![point 0 (-1) 1, point 1 0 0, point (-1) 0 0]
def face (i : Fin 4) : Set Space := {z ∈ K | inner ℝ (faceNormal i) z = faceBound i}

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI


