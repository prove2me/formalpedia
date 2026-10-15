-- Prove2me | Definitions.Def_OAI_Geometry_ProjectionBody_FacetCoordinates
-- name    : OAI_Geometry_ProjectionBody_FacetCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:22:14.823699+00:00
-- url     : https://prove2.me/theorems/cc54cb2f-8ea2-4406-9a3e-db2d1e0add60
-- title:
--   Zero-insertion isometries and the affine chart of the sum facet of a simplex
-- statement:
--   Let $n\ge0$. The file defines two maps from $\mathbb{R}^n$ to $\mathbb{R}^{n+1}$ (both Euclidean) used to parametrize the facets of the standard simplex $T_{n+1}=\operatorname{conv}\{0,e_1,\dots,e_{n+1}\}$.
--
--   1. **Zero insertion.** For a slot $i\in\{1,\dots,n+1\}$, the map $\iota_i:\mathbb{R}^n\to\mathbb{R}^{n+1}$ that inserts a zero in position $i$ and shifts the remaining coordinates:
--
--      $$\iota_i(x)=(x_1,\dots,x_{i-1},0,x_i,\dots,x_n).$$
--
--      It is a linear isometry, and its image is the coordinate hyperplane $\{y:\ y_i=0\}$, which contains the facet of $T_{n+1}$ opposite the vertex $e_i$.
--
--   2. **Sum-facet chart.** The affine map
--
--      $$\sigma_n(x)=\Bigl(x_1,\dots,x_n,\ 1-\sum_{j=1}^n x_j\Bigr),$$
--
--      whose image is the hyperplane $\{y:\ \sum_j y_j=1\}$ containing the facet of $T_{n+1}$ opposite the origin.
--
--   The accompanying simp lemmas record that $\iota_i(x)$ has $i$-th coordinate $0$ and carries the coordinates of $x$, in order, in the other slots; that $\sigma_n(x)$ has the stated coordinates; and that $\sum_j\sigma_n(x)_j=1$. Restricted to $T_n$, these maps give explicit $n$-dimensional parametrizations of the $n+2$ facets of $T_{n+1}$, which is how the facet areas entering projection volumes are computed.
--
--   **Formalization Note** `insertZero i` is a `LinearIsometry` built from `Fin.insertNth`, with its coordinates described through `Fin.succAbove` (lemmas `insertZero_same`, `insertZero_succAbove`). `sumFacetMap n` is built with `Fin.snoc` (lemmas `sumFacetMap_castSucc`, `sumFacetMap_last`, `sum_sumFacetMap`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ProjectionBody/FacetCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ProjectionBody/FacetCoordinates.lean by skeleton subtraction
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

namespace OAI

noncomputable section
open Set

namespace ProjectionCounterexample

/-- The coordinate isometry inserting a zero in slot `i`. -/
def insertZero {n : ℕ} (i : Fin (n + 1)) : E n →ₗᵢ[ℝ] E (n + 1) where
  toFun x := WithLp.toLp 2 (i.insertNth 0 x)
  map_add' x y := by
    ext j
    induction j using i.succAboveCases <;> simp
  map_smul' c x := by
    ext j
    induction j using i.succAboveCases <;> simp
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_succAbove _ i]
    simp

@[simp] theorem insertZero_same {n : ℕ} (i : Fin (n + 1)) (x : E n) :
    insertZero i x i = 0 := by simp [insertZero]

@[simp] theorem insertZero_succAbove {n : ℕ} (i : Fin (n + 1)) (x : E n)
    (j : Fin n) : insertZero i x (i.succAbove j) = x j := by simp [insertZero]

/-- The affine chart on the facet whose coordinate sum is one. -/
def sumFacetMap (n : ℕ) (x : E n) : E (n + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun j => x j) (1 - ∑ j, x j))

@[simp] theorem sumFacetMap_castSucc (n : ℕ) (x : E n) (i : Fin n) :
    sumFacetMap n x i.castSucc = x i := by simp [sumFacetMap]

@[simp] theorem sumFacetMap_last (n : ℕ) (x : E n) :
    sumFacetMap n x (Fin.last n) = 1 - ∑ j, x j := by simp [sumFacetMap]

@[simp] theorem sum_sumFacetMap (n : ℕ) (x : E n) :
    ∑ j, sumFacetMap n x j = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp

end ProjectionCounterexample

end

end OAI


