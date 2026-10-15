-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel
-- name    : OAI_Geometry_ProjectionBody_ProjectionKernel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:34:41.69004+00:00
-- url     : https://prove2.me/theorems/832b6b28-7270-429c-9a89-7ba9cebbab59
-- title:
--   Orthogonal projection onto $u^\perp$ annihilates $u$
-- statement:
--   Let $d\ge0$ and $u\in\mathbb{R}^d$, and let $P_u$ be the orthogonal projection of Euclidean $\mathbb{R}^d$ onto the hyperplane $u^\perp=\{x:\ \langle u,x\rangle=0\}$, the orthogonal complement of the line spanned by $u$. The file contains one simplification lemma: for every $u\in\mathbb{R}^d$,
--
--   $$P_u(u)=0 .$$
--
--   No normalization of $u$ is required; for $u=0$ the statement is trivial. The lemma says that the projection direction lies in the kernel of the projection, which is exactly the hypothesis needed to cover the projection of a polytope by the projections of its visible facets, those whose outer functional is positive at $u$.
--
--   **Formalization Note** The Lean statement is `project_self : project u u = 0`, where `project u` is the continuous linear map `(ℝ ∙ u)ᗮ.starProjection` from the base definitions; it is tagged `@[simp]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProjectionKernel.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProjectionKernel.lean by skeleton subtraction
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

namespace OAI

noncomputable section

namespace ProjectionCounterexample

@[simp] theorem project_self {d : ℕ} (u : E d) : project u u = 0 :=
  Submodule.starProjection_orthogonalComplement_singleton_eq_zero u

end ProjectionCounterexample

end

end OAI


