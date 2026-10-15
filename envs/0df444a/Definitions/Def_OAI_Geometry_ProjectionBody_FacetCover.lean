-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_FacetCover
-- name    : OAI_Geometry_ProjectionBody_FacetCover
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:43.039767+00:00
-- url     : https://prove2.me/theorems/4464497e-f34a-4046-8afa-924d02674956
-- title:
--   Finite intersections of halfspaces and their bounding faces
-- statement:
--   Let $V$ be a real vector space, $\iota$ a finite index set, $(a_i)_{i\in\iota}$ a family of linear functionals $a_i:V\to\mathbb{R}$, and $(b_i)_{i\in\iota}$ a family of real numbers. The file defines:
--
--   1. **Halfspace body.** The intersection of the closed halfspaces $\{a_i\le b_i\}$,
--
--      $$H(a,b)=\{x\in V:\ a_i(x)\le b_i\ \text{for all } i\in\iota\}.$$
--
--   2. **Bounding face.** For an index $i\in\iota$, the part of $H(a,b)$ lying on the $i$-th bounding hyperplane,
--
--      $$F_i(a,b)=\{x\in H(a,b):\ a_i(x)=b_i\}.$$
--
--   No nondegeneracy is assumed: a functional may vanish, an inequality may be redundant, and a face may be empty or of lower dimension. Both the standard simplex $T_d$ and the product $T_{10}\times T_{10}$ are written in this form. The faces $F_i$ are the pieces in the visible-facet description of a projection: if a linear map $q$ kills a direction $u$ with $a_i(u)>0$ for some $i$, then $q(H(a,b))$ is the union of the images $q(F_i(a,b))$ over the indices with $a_i(u)>0$.
--
--   **Formalization Note** The Lean names are `halfspaceBody a b` and `boundingFace a b i`; the index type carries a `Fintype` instance and the functionals are linear maps `V →ₗ[ℝ] ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCover.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCover.lean by skeleton subtraction
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

namespace OAI

/-! Finite-halfspace geometry underlying the visible-facet projection formula. -/

noncomputable section
open Set

namespace ProjectionCounterexample

variable {ι V W : Type*} [Fintype ι]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- A finite intersection of closed halfspaces. -/
def halfspaceBody (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set V :=
  {x | ∀ i, a i x ≤ b i}

/-- The part of the body on the bounding hyperplane of inequality `i`. -/
def boundingFace (a : ι → V →ₗ[ℝ] ℝ) (b : ι → ℝ) (i : ι) : Set V :=
  {x | x ∈ halfspaceBody a b ∧ a i x = b i}

end ProjectionCounterexample

end

end OAI


