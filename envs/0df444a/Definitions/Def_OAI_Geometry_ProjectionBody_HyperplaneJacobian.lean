-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_HyperplaneJacobian
-- name    : OAI_Geometry_ProjectionBody_HyperplaneJacobian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:32:47.390568+00:00
-- url     : https://prove2.me/theorems/1b40e6f7-78c9-4bf1-9b85-72256ac23d32
-- title:
--   Orthogonal projection from one hyperplane into another
-- statement:
--   Let $V$ be a finite-dimensional real inner product space. The file defines:
--
--   1. **Orthogonal hyperplane.** For $v\in V$, the subspace $v^\perp=\{x\in V:\ \langle v,x\rangle=0\}$, the orthogonal complement of the line $\mathbb{R}v$ (all of $V$ when $v=0$).
--
--   2. **Hyperplane-to-hyperplane projection.** For $n,u\in V$, the linear map
--
--      $$\Pi_{n,u}:n^\perp\to V,\qquad \Pi_{n,u}(x)=P_{u^\perp}(x),$$
--
--      the restriction to $n^\perp$ of the orthogonal projection $P_{u^\perp}$ of $V$ onto $u^\perp$.
--
--   When $n$ and $u$ are unit vectors, $\Pi_{n,u}$ distorts $(\dim V-1)$-dimensional volume by the factor $|\langle n,u\rangle|$, so a flat piece with unit normal $n$ and area $A$ projects onto $u^\perp$ with area $|\langle n,u\rangle|\,A$. This is the Jacobian factor behind the facet-sum formula for projection volumes of polytopes.
--
--   **Formalization Note** The Lean names are `perpendicularTo v`, an abbreviation for `(ℝ ∙ v)ᗮ`, and `hyperplaneProjection n u`, defined as the composition of `(perpendicularTo u).starProjection` with the inclusion of `perpendicularTo n`. Its codomain is all of `V` rather than the subspace $u^\perp$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/HyperplaneJacobian.lean by skeleton subtraction
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

namespace OAI

open scoped RealInnerProductSpace

namespace ProjectionCounterexample

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

abbrev perpendicularTo (v : V) : Submodule ℝ V := (ℝ ∙ v)ᗮ

/-- Restrict the actual orthogonal projection to the source tangent hyperplane. -/
def hyperplaneProjection (n u : V) : perpendicularTo n →ₗ[ℝ] V :=
  (perpendicularTo u).starProjection.toLinearMap.comp (perpendicularTo n).subtype

end

end ProjectionCounterexample

end OAI


