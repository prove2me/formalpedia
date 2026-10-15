-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionVolume_FacetAreas
-- name    : OAI_Geometry_ProjectionVolume_FacetAreas
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:02:39.431114+00:00
-- url     : https://prove2.me/theorems/d138c1e9-9fac-4304-9db4-f9f2fde03983
-- title:
--   Linear and affine charts of the facets of the simplex $T_{n+1}$
-- statement:
--   Let $n\in\mathbb{N}$, fix a position $i\in\{1,\dots,n+1\}$, and for $t\in\mathbb{R}$ and $x\in\mathbb{R}^n$ write $\operatorname{ins}_i(t,x)\in\mathbb{R}^{n+1}$ for the vector obtained by inserting $t$ as the $i$-th coordinate, the other coordinates being $x_1,\dots,x_n$ in order. The file defines:
--
--   1. **Facet embedding.** For $c\in\mathbb{R}$, the linear map $$E_{i,c}:\mathbb{R}^n\to\mathbb{R}^{n+1},\qquad E_{i,c}(x)=\operatorname{ins}_i\Bigl(c\sum_{j=1}^n x_j,\ x\Bigr).$$
--   2. **Chart of the slanted facet.** The affine map $$D_i:\mathbb{R}^n\to\mathbb{R}^{n+1},\qquad D_i(x)=\operatorname{ins}_i\Bigl(1-\sum_{j=1}^n x_j,\ x\Bigr)=E_{i,-1}(x)+e_i .$$
--
--   These charts parametrize the facets of the standard simplex $T_{n+1}=\operatorname{conv}\{0,e_1,\dots,e_{n+1}\}$ by the lower-dimensional simplex $T_n$: the map $E_{i,0}$ sends $T_n$ isometrically onto the coordinate facet $\{x\in T_{n+1}:\ x_i=0\}$, and $D_i$ sends $T_n$ onto the slanted facet $\{x\in T_{n+1}:\ \sum_j x_j=1\}$. The Gram determinant of $E_{i,c}$ equals $1+nc^2$, so the $n$-dimensional area of a coordinate facet is $1/n!$ and that of the slanted facet is $\sqrt{n+1}/n!$; these facet areas are the inputs of the brightness formula for the simplex.
--
--   **Formalization Note** `facetEmbedding n i c` is a bundled linear map `Euclidean n →ₗ[ℝ] Euclidean (n + 1)` built with `Fin.insertNth`, and `diagonalFacetChart n i` is a plain function. The position ranges over `Fin (n + 1)`, i.e. over $0,\dots,n$ in Lean's indexing. Areas are measured with the $n$-dimensional Hausdorff measure normalized to agree with Lebesgue measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionVolume/FacetAreas.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace Paper092

def facetEmbedding (n : ℕ) (i : Fin (n + 1)) (c : ℝ) :
    Euclidean n →ₗ[ℝ] Euclidean (n + 1) where
  toFun x := WithLp.toLp 2 (i.insertNth (c * ∑ j, x j) x)
  map_add' x y := by
    ext j
    induction j using i.succAboveCases <;>
      simp [PiLp.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a x := by
    ext j
    induction j using i.succAboveCases <;>
      simp [PiLp.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

def diagonalFacetChart (n : ℕ) (i : Fin (n + 1)) (x : Euclidean n) : Euclidean (n + 1) :=
  WithLp.toLp 2 (i.insertNth (1 - ∑ j, x j) x)

end Paper092

end

end OAI


