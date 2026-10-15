-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexNormals
-- name    : OAI_Geometry_ProjectionVolume_SimplexNormals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:57:04.931035+00:00
-- url     : https://prove2.me/theorems/6573ee0f-bea7-4713-a15f-328f2428a911
-- title:
--   The all-ones vector and the unit normal $\mathbf{1}/\sqrt{d}$ of the slanted facet of $T_d$
-- statement:
--   For $d\in\mathbb{N}$ the file defines two vectors of Euclidean space $\mathbb{R}^d$:
--
--   1. **Diagonal vector.** $\mathbf 1=(1,1,\dots,1)\in\mathbb{R}^d$.
--   2. **Diagonal unit normal.** $$n_d=\frac{1}{\sqrt d}\,\mathbf 1 .$$
--
--   For every $u\in\mathbb{R}^d$ one has $\langle u,\mathbf 1\rangle=\sum_i u_i$ and $\|\mathbf 1\|=\sqrt d$, and for $d\ge1$ the vector $n_d$ is a unit vector. It is the outer unit normal of the slanted facet $\{x\in T_d:\ x_1+\dots+x_d=1\}$ of the standard simplex $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}$, on which $\langle n_d,x\rangle=1/\sqrt d$; the remaining facets $\{x\in T_d:\ x_i=0\}$ have the coordinate vectors $e_i$ as unit normals. These normals enter the brightness computation through the factor $|\langle u,\nu\rangle|$ by which orthogonal projection onto $u^\perp$ scales areas inside a hyperplane with unit normal $\nu$.
--
--   **Formalization Note** The Lean names are `diagonalVector d`, defined as `WithLp.toLp 2 (1 : Fin d → ℝ)`, and `diagonalUnitNormal d = (Real.sqrt d)⁻¹ • diagonalVector d`. For $d=0$ Lean's convention that the inverse of $0$ is $0$ makes the second vector $0$, which is harmless because $\mathbb{R}^0=\{0\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/SimplexNormals.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/SimplexNormals.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionVolume mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionVolume
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexGeometry
import Definitions.Def_OAI_Geometry_ProjectionVolume_SimplexProjection
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProductProjection

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Paper092

def diagonalVector (d : ℕ) : Euclidean d := WithLp.toLp 2 (1 : Fin d → ℝ)

def diagonalUnitNormal (d : ℕ) : Euclidean d :=
  (Real.sqrt d)⁻¹ • diagonalVector d

end Paper092

end

end OAI


