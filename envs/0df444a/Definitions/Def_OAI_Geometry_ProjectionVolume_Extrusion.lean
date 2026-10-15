-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_Extrusion
-- name    : OAI_Geometry_ProjectionVolume_Extrusion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:09:21.14805+00:00
-- url     : https://prove2.me/theorems/2c0fd519-8586-4160-93e7-84ee54c02350
-- title:
--   Unit cube, extrusion cells and unit-determinant shears in $\mathbb{R}^\iota$
-- statement:
--   Let $\iota$ be a finite index set and work in the coordinate space $\mathbb{R}^\iota$ with its Lebesgue measure; $e_i$ are the standard basis vectors and $\mathbf 1$ the all-ones vector. The file defines:
--
--   1. **Unit cube.** $C=[0,1]^\iota=\{x:\ 0\le x_j\le1\ \text{for all } j\}$.
--   2. **Extrusion cell.** For $i\in\iota$, $$C_i=\{x\in\mathbb{R}^\iota:\ 1\le x_i\le2\ \text{ and }\ x_i-1\le x_j\le x_i\ \text{for all } j\ne i\}.$$
--   3. **Shear matrix.** $S_i$ is the $\iota\times\iota$ identity matrix with its $i$-th column replaced by the all-ones column, so $S_ix=x+x_i(\mathbf 1-e_i)$.
--   4. **Cell map.** $\phi_i:\mathbb{R}^\iota\to\mathbb{R}^\iota$, $$\phi_i(x)_j=\begin{cases}1+x_i, & j=i,\\ x_i+x_j, & j\ne i,\end{cases}\qquad\text{that is,}\quad \phi_i(x)=e_i+S_ix .$$
--
--   The shear has $\det S_i=1$, and the cell map $\phi_i$ sends $C$ onto $C_i$ while preserving volume, so every $C_i$ has volume $1$. For nonempty $\iota$ the Minkowski sum of the cube with the diagonal segment decomposes as $$C+[0,\mathbf 1]=C\cup\bigcup_{i\in\iota}C_i,$$ with pieces overlapping only inside hyperplanes $\{x_i=1\}$ or $\{x_i=x_j\}$; hence $\operatorname{vol}(C+[0,\mathbf 1])=|\iota|+1$. This is the volume computation behind the zonotopes that arise as projection bodies of simplices and of $T_{10}\times T_{10}$.
--
--   **Formalization Note** The Lean names are `unitCube`, `extrusionCell`, `shearMatrix` (built with `Matrix.updateCol`) and `cellMap`. The space is the function type `ι → ℝ`, and the index type carries `Fintype` and `DecidableEq` instances.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/Extrusion.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/Extrusion.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionVolume_ProjectionJacobian
import Definitions.Def_OAI_Geometry_ProjectionVolume_SupportGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Paper092

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def unitCube (ι : Type uι) : Set (ι → ℝ) := Icc 0 1

def extrusionCell (i : ι) : Set (ι → ℝ) :=
  {x | (1 ≤ x i ∧ x i ≤ 2) ∧ ∀ j, j ≠ i → x i - 1 ≤ x j ∧ x j ≤ x i}

def shearMatrix (i : ι) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ).updateCol i (fun _ => 1)

def cellMap (i : ι) (x : ι → ℝ) : ι → ℝ :=
  fun j => if j = i then 1 + x i else x i + x j

end Paper092

end OAI


