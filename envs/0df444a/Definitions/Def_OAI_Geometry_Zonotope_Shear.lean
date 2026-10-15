-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Shear
-- name    : OAI_Geometry_Zonotope_Shear
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:39:50.097706+00:00
-- url     : https://prove2.me/theorems/501c5bcd-0c00-4621-9b8c-c0468bef2d19
-- title:
--   Unit-determinant coordinate shears and the affine extrusion maps of the cube
-- statement:
--   Let $\iota$ be a finite index set with decidable equality, and work in the coordinate space $\mathbb{R}^\iota$ with standard basis $(e_j)_{j\in\iota}$ and all-ones vector $\mathbf 1=\sum_{j}e_j$. This module introduces, for each coordinate $i\in\iota$, a shear of $\mathbb{R}^\iota$ and records how it parametrizes the extrusion cells of the diagonal zonotope.
--
--   1. **Coordinate shear.** The shear $S_i:\mathbb{R}^\iota\to\mathbb{R}^\iota$ is the linear map
--   $$
--   (S_i s)_j=\begin{cases} s_i, & j=i,\\ s_j+s_i, & j\ne i,\end{cases}\qquad\text{that is,}\qquad S_i s=s+s_i\,(\mathbf 1-e_i).
--   $$
--   It adds the $i$-th coordinate to every other coordinate and leaves the $i$-th coordinate unchanged.
--
--   2. **Matrix and determinant.** In the standard basis the matrix of $S_i$ is the identity matrix with its $i$-th column replaced by the all-ones column, and
--   $$
--   \det S_i=1 .
--   $$
--
--   3. **Extrusion maps as translated shears.** The extrusion map $E_i:\mathbb{R}^\iota\to\mathbb{R}^\iota$ of the diagonal-zonotope decomposition, given by $(E_i s)_i=1+s_i$ and $(E_i s)_j=s_j+s_i$ for $j\ne i$, is the shear followed by translation by the $i$-th unit vector:
--   $$
--   E_i(s)=e_i+S_i(s)\qquad(s\in\mathbb{R}^\iota).
--   $$
--
--   The map $E_i$ carries the unit cube $[0,1]^\iota$ onto the cell $C_i=\{x:1\le x_i\le 2,\ x_i-1\le x_j\le x_i\text{ for all }j\}$ that sits over the upper facet $x_i=1$ of the cube. Because $E_i$ is a translate of a linear map of determinant $1$, it preserves Lebesgue measure; this is what makes every cell of the decomposition of the diagonal zonotope have the same volume as the cube.
--
--   **Formalization Note** `shear i` is a bundled linear map on `ι → ℝ`. The matrix identity `shear_matrix` is stated with `LinearMap.toMatrix'` and `Matrix.updateCol`, the determinant identity is `shear_det`, and `extrusionMap_eq` holds without any finiteness assumption on $\iota$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Shear.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Shear.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_ProjectionBody_ProjectionKernel
import Definitions.Def_OAI_Geometry_ProjectionBody_ProductZonotopeBridge
import Definitions.Def_OAI_Geometry_Zonotope_Determinant

namespace OAI

noncomputable section
open Set

namespace DiagonalZonotope
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The determinant-one shear that supplies the linear part of a facet extrusion. -/
def shear (i : ι) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun s j := if j = i then s i else s j + s i
  map_add' x y := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp [h, add_left_comm, add_comm]
  map_smul' c x := by
    funext j
    by_cases h : j = i
    · simp [h]
    · simp [h, mul_add]

lemma shear_matrix (i : ι) :
    LinearMap.toMatrix' (shear i) =
      (1 : Matrix ι ι ℝ).updateCol i (fun _ => 1) := by
  ext k j
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i <;>
      simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hki]
  · by_cases hki : k = i
    · subst k
      simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hji, Ne.symm hji]
    · simp [LinearMap.toMatrix'_apply, shear, Matrix.updateCol, hji, hki,
        Ne.symm hji, Pi.single_apply, Matrix.one_apply]

/-- No absolute determinant factor is lost in the extrusion parameterization. -/
theorem shear_det (i : ι) : LinearMap.det (shear i) = 1 := by
  rw [← LinearMap.det_toMatrix', shear_matrix, det_identity_updateCol_ones]

omit [Fintype ι] in
lemma extrusionMap_eq (i : ι) (s : ι → ℝ) :
    extrusionMap i s = Pi.single i 1 + shear i s := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [extrusionMap, shear]
  · simp [extrusionMap, shear, hji]

end DiagonalZonotope

end

end OAI


