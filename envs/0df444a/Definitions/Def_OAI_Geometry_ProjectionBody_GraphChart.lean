-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_GraphChart
-- name    : OAI_Geometry_ProjectionBody_GraphChart
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:43.396809+00:00
-- url     : https://prove2.me/theorems/e77c58d9-4d6e-4678-886e-18aaddc57508
-- title:
--   Linear graph charts of hyperplanes and their normal vectors
-- statement:
--   Let $n\ge0$, let $i\in\{1,\dots,n+1\}$ be a distinguished coordinate and $a\in\mathbb{R}^n$ a coefficient vector. Let $\iota_i:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the isometry inserting a zero in slot $i$, and $e_i$ the $i$-th standard basis vector of $\mathbb{R}^{n+1}$. The file defines:
--
--   1. **Graph chart.** The linear map $G_{i,a}:\mathbb{R}^n\to\mathbb{R}^{n+1}$,
--
--      $$G_{i,a}(x)=\iota_i(x)-\langle a,x\rangle\,e_i ,$$
--
--      which places the coordinates of $x$, in order, in the slots other than $i$ and the value $-\langle a,x\rangle$ in slot $i$.
--
--   2. **Graph normal.** The vector
--
--      $$N_{i,a}=\iota_i(a)+e_i\in\mathbb{R}^{n+1},$$
--
--      whose $i$-th coordinate is $1$ and whose other coordinates are those of $a$.
--
--   Since $\langle N_{i,a},G_{i,a}(x)\rangle=\langle a,x\rangle-\langle a,x\rangle=0$, the chart $G_{i,a}$ parametrizes the hyperplane $N_{i,a}^\perp$ as the graph of the $i$-th coordinate over the others, and $N_{i,a}$ is an unnormalized normal vector of that hyperplane. Facets that do not lie in coordinate hyperplanes, such as the sum facet $\sum_j y_j=1$ of a simplex, are parametrized in this form when their projected areas are computed. The simp lemmas record the $i$-th coordinates of $N_{i,a}$ and of $G_{i,a}(x)$, and the remaining coordinates of $G_{i,a}(x)$.
--
--   **Formalization Note** The Lean names are `graphLinear i a` and `graphNormal i a`, with simp lemmas `graphNormal_same`, `graphLinear_same` and `graphLinear_succAbove`; the slots other than $i$ are enumerated by `Fin.succAbove i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/GraphChart.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/GraphChart.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

/-- A graph chart with one coordinate determined by a linear equation. -/
def graphLinear {n : ℕ} (i : Fin (n + 1)) (a : E n) : E n →ₗ[ℝ] E (n + 1) where
  toFun x := insertZero i x - ⟪a, x⟫ • EuclideanSpace.single i 1
  map_add' x y := by
    simp only [map_add, inner_add_right, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, real_inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]

/-- The corresponding unnormalized normal has coordinate `i` equal to one. -/
def graphNormal {n : ℕ} (i : Fin (n + 1)) (a : E n) : E (n + 1) :=
  insertZero i a + EuclideanSpace.single i 1

@[simp] theorem graphNormal_same {n : ℕ} (i : Fin (n + 1)) (a : E n) :
    graphNormal i a i = 1 := by simp [graphNormal]

@[simp] theorem graphLinear_same {n : ℕ} (i : Fin (n + 1)) (a x : E n) :
    graphLinear i a x i = -⟪a, x⟫ := by simp [graphLinear]

@[simp] theorem graphLinear_succAbove {n : ℕ} (i : Fin (n + 1))
    (a x : E n) (j : Fin n) :
    graphLinear i a x (i.succAbove j) = x j := by simp [graphLinear]

end ProjectionCounterexample

end

end OAI


