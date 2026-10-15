-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ProductFacets
-- name    : OAI_Geometry_ProjectionBody_ProductFacets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:21:40.721299+00:00
-- url     : https://prove2.me/theorems/0fb971a5-507d-4d4e-b566-02254b392382
-- title:
--   The twenty-two facet inequalities of $T_{10}\times T_{10}$
-- statement:
--   Split $x\in\mathbb{R}^{20}$ into its blocks $x'=(x_1,\dots,x_{10})$ and $x''=(x_{11},\dots,x_{20})$, and let $\ell_\ast(y)=\sum_{i=1}^{10}y_i$, $\ell_i(y)=-y_i$ with levels $\lambda_\ast=1$, $\lambda_i=0$ be the facet functionals of the standard simplex $T_{10}\subset\mathbb{R}^{10}$. The file defines:
--
--   1. **Block projections as linear maps.** The linear maps $x\mapsto x'$ and $x\mapsto x''$ from $\mathbb{R}^{20}$ to $\mathbb{R}^{10}$.
--
--   2. **Product functionals.** Twenty-two linear functionals on $\mathbb{R}^{20}$, indexed by a block $b\in\{1,2\}$ and a simplex index $j\in\{\ast,1,\dots,10\}$:
--
--      $$L_{(1,j)}(x)=\ell_j(x'),\qquad L_{(2,j)}(x)=\ell_j(x'').$$
--
--   3. **Product levels.** $\Lambda_{(b,j)}=\lambda_j$, that is, $1$ for the two sum facets and $0$ for the twenty coordinate facets.
--
--   The inequalities $L_{(b,j)}(x)\le\Lambda_{(b,j)}$ say exactly that $x'\in T_{10}$ and $x''\in T_{10}$, so they present the product body $K=T_{10}\times T_{10}$ as a finite intersection of halfspaces, with one inequality for each of its $22$ facets.
--
--   **Formalization Note** The block index is a Boolean, `false` for the first block and `true` for the second, and the simplex index is `Option (Fin 10)`, so the index type is `Bool × Option (Fin 10)`. The Lean names are `firstBlockLinear`, `secondBlockLinear`, `productFunctional` and `productLevel`; the simp lemmas `productFunctional_first` and `productFunctional_second` unfold the functionals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ProductFacets.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ProductFacets.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

def firstBlockLinear : E 20 →ₗ[ℝ] E 10 where
  toFun := firstBlock
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def secondBlockLinear : E 20 →ₗ[ℝ] E 10 where
  toFun := secondBlock
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The twenty-two bounding inequalities of the actual Cartesian product. -/
def productFunctional : Bool × Option (Fin 10) → E 20 →ₗ[ℝ] ℝ
  | (false, i) => (simplexFunctional 10 i).comp firstBlockLinear
  | (true, i) => (simplexFunctional 10 i).comp secondBlockLinear

def productLevel (i : Bool × Option (Fin 10)) : ℝ := simplexLevel i.2

@[simp] theorem productFunctional_first (i : Option (Fin 10)) (x : E 20) :
    productFunctional (false, i) x = simplexFunctional 10 i (firstBlock x) := rfl

@[simp] theorem productFunctional_second (i : Option (Fin 10)) (x : E 20) :
    productFunctional (true, i) x = simplexFunctional 10 i (secondBlock x) := rfl

end ProjectionCounterexample

end

end OAI


