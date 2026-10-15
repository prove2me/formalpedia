-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts
-- name    : OAI_Geometry_ProjectionBody_ProductFacetCharts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:30:55.089789+00:00
-- url     : https://prove2.me/theorems/fe48bad3-0c30-4347-bfa1-97210fb649de
-- title:
--   Affine charts on the twenty-two facets of $T_{10}\times T_{10}$
-- statement:
--   Write points of $\mathbb{R}^{20}$ as $(y,w)$ with $y,w\in\mathbb{R}^{10}$, and points of $\mathbb{R}^{19}$ as pairs of blocks, either in $\mathbb{R}^9\times\mathbb{R}^{10}$ or in $\mathbb{R}^{10}\times\mathbb{R}^9$ (first and last coordinates). Let $A_j:\mathbb{R}^9\to\mathbb{R}^{10}$ and $c_j\in\mathbb{R}^{10}$, for $j\in\{\ast,1,\dots,10\}$, be the linear parts and base points of the facet charts of the simplex $T_{10}$, so that $x\mapsto c_j+A_jx$ maps $T_9$ onto the facet $j$ of $T_{10}$ (the sum facet for $j=\ast$, the coordinate facet $y_j=0$ otherwise). For the facets of $K=T_{10}\times T_{10}$, indexed by a block $b\in\{1,2\}$ and $j$, the file defines:
--
--   1. **Parameter domains.** $D_1=T_9\times T_{10}\subset\mathbb{R}^{19}$ for the facets of the first block and $D_2=T_{10}\times T_9\subset\mathbb{R}^{19}$ for those of the second block.
--
--   2. **Linear parts.** The linear maps $\mathbb{R}^{19}\to\mathbb{R}^{20}$
--
--      $$M_{(1,j)}(z,w)=(A_jz,\ w),\qquad M_{(2,j)}(z,w)=(z,\ A_jw).$$
--
--   3. **Base points.** $p_{(1,j)}=(c_j,0)$ and $p_{(2,j)}=(0,c_j)$ in $\mathbb{R}^{20}$.
--
--   The affine map $x\mapsto p_{(b,j)}+M_{(b,j)}x$ carries $D_b$ onto the facet of $K$ on which the $j$-th inequality of block $b$ is tight; for $b=1$ this is $F_j\times T_{10}$, where $F_j$ is the facet $j$ of $T_{10}$. These nineteen-dimensional parametrizations reduce the projected area of each of the $22$ facets to the volume of $D_b$ times the Jacobian of the projected chart. The simp lemmas record that the two blocks of $x\in\mathbb{R}^{20}$ are the components of the block splitting, and compute the two blocks of $M_{(b,j)}(z,w)$.
--
--   **Formalization Note** The facet index is `Bool × Option (Fin 10)`, with `false` for the first block and `true` for the second; the space `E 19` is split by `EuclideanSpace.finAddEquivProd` as $9+10$ or $10+9$. The Lean names are `productFacetDomain`, `productFacetLinear` and `productFacetCenter`, with simp lemmas `firstBlock_finAdd`, `secondBlock_finAdd` and the four lemmas `productFacetLinear_first_first`, `productFacetLinear_first_second`, `productFacetLinear_second_first`, `productFacetLinear_second_second`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetCharts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Definitions.Def_ProjectionCounterexample
import Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
import Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
import Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
import Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
import Definitions.Def_OAI_Geometry_Zonotope_Decomposition
import Definitions.Def_OAI_Geometry_Zonotope_Support
import Definitions.Def_OAI_Geometry_Zonotope_Euclidean
import Definitions.Def_OAI_Geometry_Zonotope_Product

namespace OAI

/-! Explicit nineteen-dimensional affine charts on the twenty-two product facets. -/
noncomputable section
open Set

namespace ProjectionCounterexample

/-- The product-simplex parameter domain for a facet in the selected block. -/
def productFacetDomain : Bool → Set (E 19)
  | false => (@EuclideanSpace.finAddEquivProd ℝ _ 9 10) ⁻¹'
      (simplex 9 ×ˢ simplex 10)
  | true => (@EuclideanSpace.finAddEquivProd ℝ _ 10 9) ⁻¹'
      (simplex 10 ×ˢ simplex 9)

/-- Linear part of the affine product facet chart. -/
def productFacetLinear : Bool × Option (Fin 10) → E 19 →ₗ[ℝ] E 20
  | (false, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm.toLinearMap.comp
      (((simplexFacetLinear 9 i).prodMap (LinearMap.id : E 10 →ₗ[ℝ] E 10)).comp
        (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).toLinearMap)
  | (true, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm.toLinearMap.comp
      (((LinearMap.id : E 10 →ₗ[ℝ] E 10).prodMap (simplexFacetLinear 9 i)).comp
        (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).toLinearMap)

def productFacetCenter : Bool × Option (Fin 10) → E 20
  | (false, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (simplexFacetCenter 9 i, 0)
  | (true, i) => (@EuclideanSpace.finAddEquivProd ℝ _ 10 10).symm (0, simplexFacetCenter 9 i)

@[simp] lemma firstBlock_finAdd (x : E 20) :
    ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) x).1 = firstBlock x := rfl

@[simp] lemma secondBlock_finAdd (x : E 20) :
    ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) x).2 = secondBlock x := rfl

@[simp] lemma productFacetLinear_first_first (i : Option (Fin 10)) (z : E 9) (w : E 10) :
    firstBlock (productFacetLinear (false, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, w))) = simplexFacetLinear 9 i z := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) _)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_first_second (i : Option (Fin 10)) (z : E 9) (w : E 10) :
    secondBlock (productFacetLinear (false, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (z, w))) = w := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (false, i) _)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_second_first (i : Option (Fin 10)) (z : E 10) (w : E 9) :
    firstBlock (productFacetLinear (true, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, w))) = z := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) _)).1 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

@[simp] lemma productFacetLinear_second_second (i : Option (Fin 10)) (z : E 10) (w : E 9) :
    secondBlock (productFacetLinear (true, i)
      ((@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (z, w))) = simplexFacetLinear 9 i w := by
  change ((@EuclideanSpace.finAddEquivProd ℝ _ 10 10) (productFacetLinear (true, i) _)).2 = _
  simp [productFacetLinear, LinearMap.prodMap_apply]

end ProjectionCounterexample

end

end OAI


