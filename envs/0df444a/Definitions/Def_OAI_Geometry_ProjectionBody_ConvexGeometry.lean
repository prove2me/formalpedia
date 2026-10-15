-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_ConvexGeometry
-- name    : OAI_Geometry_ProjectionBody_ConvexGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:18.109367+00:00
-- url     : https://prove2.me/theorems/e0669272-79cf-4122-b862-a40cc5d2245e
-- title:
--   Block splitting of $\mathbb{R}^{20}$ as $\mathbb{R}^{10}\times\mathbb{R}^{10}$
-- statement:
--   This file defines a single object, the block splitting map
--
--   $$\beta:\mathbb{R}^{20}\to\mathbb{R}^{10}\times\mathbb{R}^{10},\qquad \beta(x)=\bigl((x_1,\dots,x_{10}),\,(x_{11},\dots,x_{20})\bigr)=(x',x''),$$
--
--   which separates the first ten and the last ten coordinates of a point of Euclidean $\mathbb{R}^{20}$. It is a continuous linear isomorphism of real vector spaces with continuous inverse.
--
--   Its role is to transport topological and convexity properties between $\mathbb{R}^{20}$ and the product of two copies of $\mathbb{R}^{10}$. The product body $K=T_{10}\times T_{10}$ is exactly the preimage $\beta^{-1}(T_{10}\times T_{10})$, so that compactness, convexity and the existence of interior points of $K$ follow from the corresponding properties of the standard simplex $T_{10}=\operatorname{conv}\{0,e_1,\dots,e_{10}\}$.
--
--   **Formalization Note** `blockEquiv : E 20 ≃L[ℝ] E 10 × E 10` is Mathlib's `EuclideanSpace.finAddEquivProd` specialized to $n=m=10$; it is recorded as a continuous linear equivalence, not as an isometry.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/ConvexGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/ConvexGeometry.lean by skeleton subtraction
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

namespace OAI

open Set

namespace ProjectionCounterexample

noncomputable section

def blockEquiv : E 20 ≃L[ℝ] E 10 × E 10 :=
  EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 10) (m := 10)

end

end ProjectionCounterexample

end OAI


