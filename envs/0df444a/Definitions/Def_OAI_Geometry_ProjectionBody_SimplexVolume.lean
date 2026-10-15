-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_SimplexVolume
-- name    : OAI_Geometry_ProjectionBody_SimplexVolume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:34:20.581349+00:00
-- url     : https://prove2.me/theorems/eb910e68-606a-474b-ba3b-760c5890eaf5
-- title:
--   Coordinate simplices of radius $r$ and products of two unit simplices
-- statement:
--   Let $n,p,q\ge0$ and $r\in\mathbb{R}$, and consider the coordinate spaces $\mathbb{R}^n$ and $\mathbb{R}^{p+q}$ with Lebesgue measure. The file defines:
--
--   1. **Coordinate simplex of radius $r$.**
--
--      $$\Delta_n(r)=\Bigl\{x\in\mathbb{R}^n:\ x_i\ge0\ \text{for all } i,\ \ \sum_{i=1}^n x_i\le r\Bigr\}.$$
--
--      For $r\ge0$ this is the simplex with vertices $0,re_1,\dots,re_n$; for $r<0$ it is empty.
--
--   2. **Product of two unit simplices.** Writing $x\in\mathbb{R}^{p+q}$ as $(x',x'')$ with $x'\in\mathbb{R}^p$ its first $p$ and $x''\in\mathbb{R}^q$ its last $q$ coordinates,
--
--      $$\Delta_{p,q}=\{x\in\mathbb{R}^{p+q}:\ x'\in\Delta_p(1)\ \text{and}\ x''\in\Delta_q(1)\}=\Delta_p(1)\times\Delta_q(1).$$
--
--   These are the sets whose Lebesgue volumes, $r^n/n!$ for $r\ge0$ and $1/(p!\,q!)$, are computed in the accompanying results. The Euclidean standard simplex $T_n=\operatorname{conv}\{0,e_1,\dots,e_n\}$ and the product $T_{10}\times T_{10}$ are identified with $\Delta_n(1)$ and $\Delta_{10,10}$ to obtain their volumes $1/n!$ and $1/(10!)^2$.
--
--   **Formalization Note** Both sets live in the plain function spaces `Fin n → ℝ` and `Fin (p + q) → ℝ` with the product Lebesgue measure, not in `EuclideanSpace`; transfer to Euclidean space uses a measure-preserving equivalence. The Lean names are `coordinateSimplex n r` and `coordinateSimplexProduct p q`, and the blocks are extracted with `Fin.castAdd q` and `Fin.natAdd p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/SimplexVolume.lean by skeleton subtraction
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

namespace OAI

/-!
# Volumes of standard simplices and their products

The simplex-volume calculation below uses Tonelli's theorem and induction on the
dimension.  At first coordinate `t`, the remaining section is a simplex of radius
`r - t`; its volume is integrated over `0 ≤ t ≤ r`.  The Euclidean versions use
the measure-preserving equivalence between coordinate space and `EuclideanSpace`.
The product formula is proved using the product Lebesgue measure under the
canonical splitting of `Fin (p + q)`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProjectionCounterexample

/-- The coordinate standard simplex with nonnegative coordinates and sum at most `r`. -/
def coordinateSimplex (n : ℕ) (r : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ r}

/-- The coordinate product, with the first `p` and last `q` coordinates separated. -/
def coordinateSimplexProduct (p q : ℕ) : Set (Fin (p + q) → ℝ) :=
  {x | (fun i : Fin p => x (Fin.castAdd q i)) ∈ coordinateSimplex p 1 ∧
    (fun i : Fin q => x (Fin.natAdd p i)) ∈ coordinateSimplex q 1}

end ProjectionCounterexample

end OAI


