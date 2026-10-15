-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Decomposition
-- name    : OAI_Geometry_Zonotope_Decomposition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:25:58.789694+00:00
-- url     : https://prove2.me/theorems/2ac152e7-980e-471d-8796-fab87516bc0e
-- title:
--   The cube-plus-diagonal zonotope, its extrusion cells and their affine parametrization
-- statement:
--   Let $\iota$ be an index set and consider the coordinate space $\mathbb{R}^\iota$ of real functions on $\iota$, with all-ones vector $\mathbf 1$ and unit vectors $e_i$. The file defines:
--
--   1. **Unit cube.** $C=[0,1]^\iota=\{x:\ 0\le x_j\le1\ \text{for all } j\}$.
--
--   2. **Diagonal zonotope.** The Minkowski sum of the cube and the diagonal unit segment,
--
--      $$Z=C+[0,1]\,\mathbf 1=\{q+t\mathbf 1:\ q\in C,\ t\in[0,1]\}.$$
--
--   3. **Extrusion cells.** For $i\in\iota$, the region swept out by the upper facet $\{x_i=1\}$ of the cube as it is translated along the diagonal segment:
--
--      $$C_i=\{x:\ 1\le x_i\le2\ \text{and}\ x_i-1\le x_j\le x_i\ \text{for all } j\}.$$
--
--   4. **Extrusion map.** For $i\in\iota$, the affine map $\varphi_i:\mathbb{R}^\iota\to\mathbb{R}^\iota$ with $\varphi_i(s)_i=1+s_i$ and $\varphi_i(s)_j=s_j+s_i$ for $j\neq i$; in other words $\varphi_i(s)=e_i+S_is$, where the shear $S_i$ adds $s_i$ to every coordinate other than the $i$-th.
--
--   5. **Cells are affine images of the cube.** For every $i\in\iota$,
--
--      $$C_i=\varphi_i(C).$$
--
--   When $\iota$ is finite, $Z$ is the union of the cube and the cells $C_i$, any two of which overlap only inside a hyperplane, and item 5 exhibits every cell as an image of the unit cube under a determinant-one affine map; together these give $\operatorname{vol}(Z)=|\iota|+1$. For $\iota=\{1,\dots,d\}$, a translated and rescaled copy of $Z$ is the projection body of the standard simplex $T_d$.
--
--   **Formalization Note** The sets live in the plain function space `ι → ℝ`, not in `EuclideanSpace`, and no finiteness of `ι` is assumed in these definitions. The Lean names are `cube`, `zonotope`, `cell`, `extrusionMap` (which requires decidable equality on `ι`) and the theorem `cell_eq_image_cube`. The two private lemmas `ite_eq_left` and `ite_eq_right` are local restatements of `if_pos` and `if_neg` used in its proof.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Decomposition.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Decomposition.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-!
The unit cube extruded by the segment from zero to the all-ones vector.
Its decomposition uses the cube and one extrusion cell for every upper facet.
The set definitions are literal subsets of a finite real coordinate space.
-/

noncomputable section
open Set

namespace DiagonalZonotope

variable {ι : Type*}

/-- The actual unit cube in the coordinate space. -/
def cube : Set (ι → ℝ) := {x | ∀ j, 0 ≤ x j ∧ x j ≤ 1}

/-- The Minkowski sum of the unit cube and the diagonal unit segment. -/
def zonotope : Set (ι → ℝ) :=
  {x | ∃ q ∈ cube, ∃ t ∈ Icc (0 : ℝ) 1, x = q + t • (1 : ι → ℝ)}

/-- The extrusion of the upper facet normal to coordinate `i`. -/
def cell (i : ι) : Set (ι → ℝ) :=
  {x | 1 ≤ x i ∧ x i ≤ 2 ∧ ∀ j, x i - 1 ≤ x j ∧ x j ≤ x i}

section AffineCell
variable [DecidableEq ι]

/-- A shear of the cube followed by translation by the `i`th unit vector. -/
def extrusionMap (i : ι) (s : ι → ℝ) : ι → ℝ :=
  fun j => if j = i then 1 + s i else s j + s i

/-- Each extrusion cell is an actual affine image of the unit cube. -/
theorem cell_eq_image_cube (i : ι) : cell i = extrusionMap i '' cube := by
  apply Subset.antisymm
  · intro x hx
    let s : ι → ℝ := fun j => if j = i then x i - 1 else x j - (x i - 1)
    refine ⟨s, ?_, ?_⟩
    · intro j
      by_cases hji : j = i
      · subst j
        simp only [s, ite_eq_left rfl]
        constructor <;> linarith [hx.1, hx.2.1]
      · simp only [s, ite_eq_right hji]
        constructor <;> linarith [(hx.2.2 j).1, (hx.2.2 j).2]
    · funext j
      by_cases hji : j = i
      · subst j
        simp [extrusionMap, s]
      · simp [extrusionMap, s, hji]
  · rintro x ⟨s, hs, rfl⟩
    have hi : extrusionMap i s i = 1 + s i := by simp [extrusionMap]
    refine ⟨?_, ?_, ?_⟩
    · rw [hi]
      linarith [(hs i).1]
    · rw [hi]
      linarith [(hs i).2]
    · intro j
      by_cases hji : j = i
      · subst j
        exact ⟨by linarith, le_rfl⟩
      · simp only [extrusionMap, ite_eq_right hji, ite_true]
        constructor <;> linarith [(hs j).1, (hs j).2]

end AffineCell
end DiagonalZonotope

end

end OAI


