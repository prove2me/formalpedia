-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Euclidean
-- name    : OAI_Geometry_Zonotope_Euclidean
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:27:15.718199+00:00
-- url     : https://prove2.me/theorems/46ec66f7-999d-4bec-b1fc-8823af43af64
-- title:
--   Scaled Euclidean copies of the centered zonotope and its support value
-- statement:
--   Let $\iota$ be a finite index set and $Z_0=[-\tfrac12,\tfrac12]^\iota+[-\tfrac12,\tfrac12]\mathbf 1$ the origin-centered Minkowski sum of a unit cube and the diagonal segment. The file defines:
--
--   1. **Scaled Euclidean zonotope.** For $c\in\mathbb{R}$, the set
--
--      $$cZ_0=\{c\,y:\ y\in Z_0\},$$
--
--      regarded as a subset of the Euclidean space $\mathbb{R}^\iota$ with its standard inner product.
--
--   2. **Support value.** For $u\in\mathbb{R}^\iota$,
--
--      $$h(u)=\frac12\Bigl(\sum_{i\in\iota}|u_i|+\Bigl|\sum_{i\in\iota}u_i\Bigr|\Bigr).$$
--
--   For $c>0$ the support function of $cZ_0$ is $c\,h$, that is, $cZ_0=\{x:\ \langle u,x\rangle\le c\,h(u)\ \text{for all } u\}$. For the standard simplex $T_d\subset\mathbb{R}^d$ with $d\ge2$, the projection volumes are $|T_d|u^\perp|=h(u)/(d-1)!$ for unit vectors $u$, so its projection body is $\frac{1}{(d-1)!}Z_0$; these two objects carry that identification and the subsequent volume computation.
--
--   **Formalization Note** `DiagonalZonotope.euclidean c` is the image of `c • centered` under `WithLp.toLp 2`, a subset of `EuclideanSpace ℝ ι`; `DiagonalZonotope.support u` takes a plain function `u : ι → ℝ`, so Euclidean vectors enter it through `WithLp.ofLp`. No sign condition on $c$ is imposed in the definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Euclidean.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Euclidean.lean by skeleton subtraction
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

namespace OAI

/-! Coordinate and Euclidean versions of the explicit centered zonotope. -/
noncomputable section
open Set
open scoped BigOperators RealInnerProductSpace

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

/-- The actual scalar image of the cube-plus-diagonal body in Euclidean space. -/
def euclidean (c : ℝ) : Set (EuclideanSpace ℝ ι) :=
  WithLp.toLp 2 '' ((fun y : ι → ℝ => c • y) '' centered)

/-- The directional support value, before multiplication by the scale. -/
def support (u : ι → ℝ) : ℝ := ((∑ i, |u i|) + |∑ i, u i|) / 2

end DiagonalZonotope

end

end OAI


