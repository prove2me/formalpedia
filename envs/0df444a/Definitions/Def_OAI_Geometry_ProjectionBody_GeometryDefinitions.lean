-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_GeometryDefinitions
-- name    : OAI_Geometry_ProjectionBody_GeometryDefinitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:18:40.88458+00:00
-- url     : https://prove2.me/theorems/63010217-9bf1-44a5-9941-d52b8e94c226
-- title:
--   The block decomposition of $\mathbb{R}^{20}$ and the product body $T_{10}\times T_{10}$
-- statement:
--   Let $\mathbb{R}^d$ carry its standard Euclidean structure and let $T_d=\operatorname{conv}\{0,e_1,\dots,e_d\}$ be the standard simplex spanned by the origin and the standard basis vectors. Write a point of $\mathbb{R}^{20}$ as $x=(x_1,\dots,x_{20})$. The file defines:
--
--   1. **First block.** $x'=(x_1,\dots,x_{10})\in\mathbb{R}^{10}$, the first ten coordinates of $x$.
--
--   2. **Second block.** $x''=(x_{11},\dots,x_{20})\in\mathbb{R}^{10}$, the last ten coordinates of $x$.
--
--   3. **Product body.** The Cartesian product of two copies of $T_{10}$, realized inside $\mathbb{R}^{20}$:
--
--      $$K=\{x\in\mathbb{R}^{20}:\ x'\in T_{10}\ \text{and}\ x''\in T_{10}\}=T_{10}\times T_{10}.$$
--
--   The maps $x\mapsto x'$ and $x\mapsto x''$ are the two coordinate projections of the orthogonal decomposition $\mathbb{R}^{20}=\mathbb{R}^{10}\oplus\mathbb{R}^{10}$. The body $K$ is the explicit competitor whose projection-body ratio is compared with that of the simplex $T_{20}$; its facets, projection volumes and volume are all computed through these two blocks.
--
--   **Formalization Note** The ambient space is `E 20`, i.e. `EuclideanSpace ℝ (Fin 20)`, with coordinates indexed from $0$; the first block uses the indices `Fin.castAdd 10 i` and the second block the indices `Fin.natAdd 10 i` for `i : Fin 10`. The simplex is `simplex 10` from the base definitions, and the Lean names are `firstBlock`, `secondBlock` and `productBody`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/GeometryDefinitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/GeometryDefinitions.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

/-- The first ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def firstBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.castAdd 10 i)

/-- The last ten coordinates in the standard orthogonal decomposition of R²⁰. -/
def secondBlock (x : E 20) : E 10 :=
  WithLp.toLp 2 fun i : Fin 10 => x (Fin.natAdd 10 i)

/-- The genuine Cartesian product T₁₀ × T₁₀ in Euclidean R²⁰. -/
def productBody : Set (E 20) :=
  {x | firstBlock x ∈ simplex 10 ∧ secondBlock x ∈ simplex 10}

end ProjectionCounterexample

end

end OAI


