-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Support
-- name    : OAI_Geometry_Zonotope_Support
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:26:45.707318+00:00
-- url     : https://prove2.me/theorems/294f9f34-0ddd-4ad5-b4d0-06361241b344
-- title:
--   The origin-centered cube-plus-diagonal zonotope
-- statement:
--   Let $\iota$ be a finite index set, $\mathbf 1\in\mathbb{R}^\iota$ the all-ones vector and $Z=[0,1]^\iota+[0,1]\,\mathbf 1$ the Minkowski sum of the unit cube and the diagonal unit segment. The file defines the translate of $Z$ centered at the origin:
--
--   $$Z_0=\{x\in\mathbb{R}^\iota:\ x+\mathbf 1\in Z\}=Z-\mathbf 1=\bigl[-\tfrac12,\tfrac12\bigr]^\iota+\bigl[-\tfrac12,\tfrac12\bigr]\mathbf 1 .$$
--
--   Both the cube and the segment have center $\tfrac12\mathbf 1$, so $\mathbf 1$ is the center of symmetry of $Z$ and $Z_0$ is symmetric about the origin. This is the convenient normalization for support-function computations: the support function of $Z_0$ in direction $u$ is $\frac12\bigl(\sum_i|u_i|+|\sum_i u_i|\bigr)$, the sum of the support functions of the centered cube and the centered segment, and $Z_0$ is cut out by the inequalities $|x_i|\le1$ and $|x_i-x_j|\le1$. Scaled copies of $Z_0$ are the projection bodies of the standard simplex and, blockwise, of the product of two simplices.
--
--   **Formalization Note** The Lean name is `DiagonalZonotope.centered`, a subset of the function space `ι → ℝ` defined by the condition `(fun j => x j + 1) ∈ zonotope`; the index type carries a `Fintype` instance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Support.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Support.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set
open scoped BigOperators

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι]

/-- The translate of the diagonal zonotope centered at the origin. -/
def centered : Set (ι → ℝ) := {x | (fun j => x j + 1) ∈ zonotope}

end DiagonalZonotope

end

end OAI


