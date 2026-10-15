-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Product
-- name    : OAI_Geometry_Zonotope_Product
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:29:30.906288+00:00
-- url     : https://prove2.me/theorems/916b77ce-2e33-4320-9b7d-0abadddf1ed8
-- title:
--   Block product of two scaled centered zonotopes
-- statement:
--   Let $n,m\ge0$ and $c\in\mathbb{R}$, and for $k\ge0$ let $cZ^{(k)}=c\bigl([-\tfrac12,\tfrac12]^k+[-\tfrac12,\tfrac12]\mathbf 1\bigr)$ be the scaled origin-centered cube-plus-diagonal zonotope in Euclidean $\mathbb{R}^k$. Split $x\in\mathbb{R}^{n+m}$ as $x=(x',x'')$ with $x'\in\mathbb{R}^n$ its first $n$ and $x''\in\mathbb{R}^m$ its last $m$ coordinates. The file defines
--
--   $$P_{n,m}(c)=\{x\in\mathbb{R}^{n+m}:\ x'\in cZ^{(n)}\ \text{and}\ x''\in cZ^{(m)}\}=cZ^{(n)}\times cZ^{(m)} .$$
--
--   This is the shape of the projection body of a product of two simplices: if a body in $\mathbb{R}^{n+m}$ has projection volumes $c\bigl(h(u')+h(u'')\bigr)$ for all unit $u$, with $c>0$ and $h(v)=\frac12\bigl(\sum_i|v_i|+|\sum_i v_i|\bigr)$, then its projection body is $P_{n,m}(c)$. Its volume is the product of the two block volumes.
--
--   **Formalization Note** `DiagonalZonotope.euclideanProduct n m c` is the preimage of `euclidean c ×ˢ euclidean c` under `EuclideanSpace.finAddEquivProd`, the linear splitting of `EuclideanSpace ℝ (Fin (n + m))` into its first $n$ and last $m$ coordinates.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Product.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Product.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace DiagonalZonotope

/-- The two-block product of explicit Euclidean zonotopes. -/
def euclideanProduct (n m : ℕ) (c : ℝ) : Set (EuclideanSpace ℝ (Fin (n + m))) :=
  EuclideanSpace.finAddEquivProd ⁻¹'
    ((euclidean c : Set (EuclideanSpace ℝ (Fin n))) ×ˢ euclidean c)

end DiagonalZonotope

end

end OAI


