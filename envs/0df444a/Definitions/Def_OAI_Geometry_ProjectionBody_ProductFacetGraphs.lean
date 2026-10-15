-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
-- name    : OAI_Geometry_ProjectionBody_ProductFacetGraphs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:31:59.060956+00:00
-- url     : https://prove2.me/theorems/9b9fd0e0-b621-4205-bf16-c6630d5a5d2b
-- title:
--   Graph coefficient vectors for the two sum facets of $T_{10}\times T_{10}$
-- statement:
--   Write points of $\mathbb{R}^{19}$ as concatenations of two blocks, either in $\mathbb{R}^9\times\mathbb{R}^{10}$ or in $\mathbb{R}^{10}\times\mathbb{R}^9$, and let $\mathbf 1_9$ be the all-ones vector of $\mathbb{R}^9$. The file defines:
--
--   1. **First sum-facet coefficient vector.** $g_1=(\mathbf 1_9,\,0)\in\mathbb{R}^9\times\mathbb{R}^{10}=\mathbb{R}^{19}$: ones in the first nine coordinates and zeros in the last ten.
--
--   2. **Second sum-facet coefficient vector.** $g_2=(0,\,\mathbf 1_9)\in\mathbb{R}^{10}\times\mathbb{R}^9=\mathbb{R}^{19}$: zeros in the first ten coordinates and ones in the last nine.
--
--   3. **Coordinates of a concatenation.** For $x\in\mathbb{R}^n$ and $y\in\mathbb{R}^m$, the concatenated vector $(x,y)\in\mathbb{R}^{n+m}$ has coordinate $x_i$ in position $i$ and coordinate $y_i$ in position $n+i$.
--
--   In $K=T_{10}\times T_{10}\subset\mathbb{R}^{20}$, the linear part of the chart of the sum facet $\sum_{k=1}^{10}y_k=1$ of the first factor is the graph chart over $\mathbb{R}^{19}$ whose tenth coordinate equals $-\langle g_1,x\rangle$, and for the second factor the twentieth coordinate equals $-\langle g_2,x\rangle$. The corresponding graph normals are $(\mathbf 1_{10},0)$ and $(0,\mathbf 1_{10})$, which is how the area factors of the two sum facets are obtained.
--
--   **Formalization Note** The Lean names are `firstSumGraph` and `secondSumGraph`, both elements of `E 19` built with `EuclideanSpace.finAddEquivProd`, and the simp lemmas `blockJoin_first` and `blockJoin_second`, which use the indices `Fin.castAdd m i` and `Fin.natAdd n i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacetGraphs.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetCharts

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- Graph coefficient vector for the first block's sum facet. -/
def firstSumGraph : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 9 10).symm (allOnes 9, 0)

/-- Graph coefficient vector for the second block's sum facet. -/
def secondSumGraph : E 19 := (@EuclideanSpace.finAddEquivProd ℝ _ 10 9).symm (0, allOnes 9)

@[simp] lemma blockJoin_first {n m : ℕ} (x : E n) (y : E m) (i : Fin n) :
    (@EuclideanSpace.finAddEquivProd ℝ _ n m).symm (x, y) (i.castAdd m) = x i := by
  exact congrArg (fun z : E n × E m => z.1 i)
    ((@EuclideanSpace.finAddEquivProd ℝ _ n m).apply_symm_apply (x, y))

@[simp] lemma blockJoin_second {n m : ℕ} (x : E n) (y : E m) (i : Fin m) :
    (@EuclideanSpace.finAddEquivProd ℝ _ n m).symm (x, y) (i.natAdd n) = y i := by
  exact congrArg (fun z : E n × E m => z.2 i)
    ((@EuclideanSpace.finAddEquivProd ℝ _ n m).apply_symm_apply (x, y))

end ProjectionCounterexample

end

end OAI


