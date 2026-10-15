-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ProductZonotopeBridge
-- name    : OAI_Geometry_ProjectionBody_ProductZonotopeBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:36:15.369412+00:00
-- url     : https://prove2.me/theorems/383d9719-757d-4a25-bf78-149f5b4a687e
-- title:
--   Sum of the two block support values on $\mathbb{R}^{n+m}$
-- statement:
--   Let $n,m\ge0$ and, for $k\ge0$, let
--
--   $$h_k(v)=\frac12\Bigl(\sum_{i=1}^k|v_i|+\Bigl|\sum_{i=1}^k v_i\Bigr|\Bigr),\qquad v\in\mathbb{R}^k ,$$
--
--   be the support value of the origin-centered cube-plus-diagonal zonotope in $\mathbb{R}^k$. For $u\in\mathbb{R}^{n+m}$, split as $u=(u',u'')$ with $u'\in\mathbb{R}^n$ its first $n$ and $u''\in\mathbb{R}^m$ its last $m$ coordinates, the file defines the block support value
--
--   $$h_{n,m}(u)=h_n(u')+h_m(u'').$$
--
--   For $c>0$, $c\,h_{n,m}$ is the support function of the product $cZ^{(n)}\times cZ^{(m)}$ of two scaled centered zonotopes, since the support function of a product is the sum of the support functions of its factors. The projection volumes of the product of simplices $K=T_{10}\times T_{10}$ have exactly this form, $|K|u^\perp|=h_{10,10}(u)/(9!\,10!)$ for unit $u$, which identifies its projection body with such a product of zonotopes.
--
--   **Formalization Note** The Lean name is `blockSupport u` with implicit `n m`; the blocks are obtained with `EuclideanSpace.finAddEquivProd` and converted to plain functions with `WithLp.ofLp` before applying `DiagonalZonotope.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductZonotopeBridge.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductZonotopeBridge.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacetGraphs
import Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
import Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- The sum of the two block support functions, with a common scale. -/
def blockSupport {n m : ℕ} (u : E (n + m)) : ℝ :=
  DiagonalZonotope.support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).1) +
  DiagonalZonotope.support (WithLp.ofLp (EuclideanSpace.finAddEquivProd u).2)

end ProjectionCounterexample

end

end OAI


