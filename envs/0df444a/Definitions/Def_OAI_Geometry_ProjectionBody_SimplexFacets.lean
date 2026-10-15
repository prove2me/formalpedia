-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_SimplexFacets
-- name    : OAI_Geometry_ProjectionBody_SimplexFacets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:20:33.340652+00:00
-- url     : https://prove2.me/theorems/ce0cea55-e321-4e46-a3fd-a8cd4de5d2a7
-- title:
--   Facet-defining linear functionals of the standard simplex
-- statement:
--   Let $d\ge0$ and write points of Euclidean $\mathbb{R}^d$ as $x=(x_1,\dots,x_d)$. The file defines:
--
--   1. **Coordinate functionals.** For $i\in\{1,\dots,d\}$, the linear functional $\pi_i(x)=x_i$.
--
--   2. **Simplex functionals.** A family of $d+1$ linear functionals indexed by $\{\ast\}\cup\{1,\dots,d\}$:
--
--      $$\ell_\ast(x)=\sum_{i=1}^d x_i,\qquad \ell_i(x)=-x_i\quad(1\le i\le d).$$
--
--   3. **Simplex levels.** The right-hand sides $\lambda_\ast=1$ and $\lambda_i=0$ for $1\le i\le d$.
--
--   The inequalities $\ell_j(x)\le\lambda_j$ read $\sum_i x_i\le1$ and $x_i\ge0$; they are the $d+1$ facet inequalities of the standard simplex $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}$, and each $\ell_j$ is an outward normal functional of the corresponding facet. Writing $T_d$ as the halfspace body of this family allows the general facet machinery for finite intersections of halfspaces to be applied to the simplex.
--
--   **Formalization Note** The index set is `Option (Fin d)`, with `none` for the sum facet and `some i` for the coordinate facet $x_i=0$. The Lean names are `coordinateFunctional`, `simplexFunctional` and `simplexLevel`; the simp lemmas `coordinateFunctional_apply`, `simplexFunctional_none` and `simplexFunctional_some` evaluate them.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexFacets.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

/-- Coordinate linear functional on the Euclidean space. -/
def coordinateFunctional {d : ℕ} (i : Fin d) : E d →ₗ[ℝ] ℝ where
  toFun x := x i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateFunctional_apply {d : ℕ} (i : Fin d) (x : E d) :
    coordinateFunctional i x = x i := rfl

/-- Outward defining functionals: the sum facet, then the coordinate facets. -/
def simplexFunctional (d : ℕ) : Option (Fin d) → E d →ₗ[ℝ] ℝ
  | none => ∑ i, coordinateFunctional i
  | some i => -coordinateFunctional i

def simplexLevel {d : ℕ} : Option (Fin d) → ℝ
  | none => 1
  | some _ => 0

@[simp] theorem simplexFunctional_none (d : ℕ) (x : E d) :
    simplexFunctional d none x = ∑ i, x i := by
  simp [simplexFunctional]

@[simp] theorem simplexFunctional_some {d : ℕ} (i : Fin d) (x : E d) :
    simplexFunctional d (some i) x = -x i := rfl

end ProjectionCounterexample

end

end OAI


