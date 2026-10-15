-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacetCharts
-- name    : OAI_Geometry_ProjectionBody_SimplexFacetCharts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:38.091775+00:00
-- url     : https://prove2.me/theorems/5a96c275-80cf-4168-80cf-a4dfafc3df83
-- title:
--   Affine parametrizations of the facets of the standard simplex
-- statement:
--   Let $n\ge0$, let $\iota_i:\mathbb{R}^n\to\mathbb{R}^{n+1}$ be the isometry inserting a zero in slot $i$, and let $G_{i,a}(x)=\iota_i(x)-\langle a,x\rangle e_i$ be the linear graph chart with coefficient vector $a$. The facets of $T_{n+1}=\operatorname{conv}\{0,e_1,\dots,e_{n+1}\}$ are indexed by $\ast$ (the sum facet $\sum_k y_k=1$) and by $i\in\{1,\dots,n+1\}$ (the coordinate facet $y_i=0$). The file defines:
--
--   1. **All-ones vector.** $\mathbf 1_n=(1,\dots,1)\in\mathbb{R}^n$, together with the identities $(\mathbf 1_n)_i=1$ and $\langle\mathbf 1_n,x\rangle=\sum_i x_i$.
--
--   2. **Linear parts of the facet charts.** Linear maps $A_j:\mathbb{R}^n\to\mathbb{R}^{n+1}$ given by
--
--      $$A_\ast=G_{n+1,\mathbf 1_n},\quad\text{i.e.}\quad A_\ast(x)=\Bigl(x_1,\dots,x_n,\ -\sum_{k=1}^n x_k\Bigr),\qquad A_i=\iota_i .$$
--
--   3. **Base points.** $c_\ast=e_{n+1}$ and $c_i=0$.
--
--   The affine map $x\mapsto c_j+A_jx$ carries the simplex $T_n$ onto the facet $j$ of $T_{n+1}$: for $j=\ast$ it is the chart $x\mapsto\bigl(x,\,1-\sum_k x_k\bigr)$ of the sum facet, and for $j=i$ it inserts a zero coordinate. With the linear parts explicit, the area factor of each projected facet is the Jacobian of an orthogonal projection composed with $A_j$.
--
--   **Formalization Note** The facet index is `Option (Fin (n + 1))`, matching `simplexFunctional (n + 1)`. The Lean names are `allOnes`, `simplexFacetLinear` and `simplexFacetCenter`, with simp lemmas `allOnes_apply` and `inner_allOnes`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexFacetCharts.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexFacetCharts.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace ProjectionCounterexample

def allOnes (n : ℕ) : E n := WithLp.toLp 2 (fun _ => 1)

@[simp] theorem allOnes_apply {n : ℕ} (i : Fin n) : allOnes n i = 1 := rfl

@[simp] theorem inner_allOnes {n : ℕ} (x : E n) : ⟪allOnes n, x⟫ = ∑ i, x i := by
  simp [PiLp.inner_apply, allOnes]

/-- Linear part of each simplex facet chart. -/
def simplexFacetLinear (n : ℕ) : Option (Fin (n + 1)) → E n →ₗ[ℝ] E (n + 1)
  | none => graphLinear (Fin.last n) (allOnes n)
  | some i => (insertZero i).toLinearMap

def simplexFacetCenter (n : ℕ) : Option (Fin (n + 1)) → E (n + 1)
  | none => EuclideanSpace.single (Fin.last n) 1
  | some _ => 0

end ProjectionCounterexample

end

end OAI


