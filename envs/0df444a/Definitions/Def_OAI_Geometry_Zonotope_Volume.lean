-- Prove2me | Definitions.Def_OAI_Geometry_Zonotope_Volume
-- name    : OAI_Geometry_Zonotope_Volume
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:40:26.47819+00:00
-- url     : https://prove2.me/theorems/fe178931-bdfe-4f6a-8a37-4d2b8ed9f390
-- title:
--   Unit Lebesgue volume of the cube and of each extrusion cell
-- statement:
--   Let $\iota$ be a finite index set and equip $\mathbb{R}^\iota$ with Lebesgue measure $\lambda$ (the product of the one-dimensional Lebesgue measures). Consider the unit cube $Q=\{x\in\mathbb{R}^\iota:0\le x_j\le 1\text{ for all }j\}$ and, for $i\in\iota$, the extrusion cell
--   $$
--   C_i=\{x\in\mathbb{R}^\iota:\ 1\le x_i\le 2,\ \ x_i-1\le x_j\le x_i\ \text{ for all } j\in\iota\}.
--   $$
--   This module records three facts about these sets.
--
--   1. **The cube is a box.** $Q=\prod_{j\in\iota}[0,1]$, the product of unit intervals.
--
--   2. **Volume of the cube.** $\lambda(Q)=1$.
--
--   3. **Volume of a cell.** $\lambda(C_i)=1$ for every $i\in\iota$.
--
--   The diagonal zonotope $Z=[0,1]^\iota+[0,1]\,\mathbf 1$ is the union of $Q$ and the $|\iota|$ cells $C_i$, and these pieces overlap only in Lebesgue-null sets; the unit volumes recorded here are therefore exactly the summands in the formula $\lambda(Z)=|\iota|+1$, from which the volumes of the zonotopal projection bodies in this development are computed.
--
--   **Formalization Note** The measure is Mathlib's `volume` on `ι → ℝ`, with values in `ℝ≥0∞`. The box identity `cube_eq_pi` needs no finiteness, `volume_cube` needs `[Fintype ι]`, and `volume_cell` additionally uses `[DecidableEq ι]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Zonotope/Volume.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Zonotope/Volume.lean by skeleton subtraction
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
import Definitions.Def_OAI_Geometry_Zonotope_Shear

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace DiagonalZonotope

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma cube_eq_pi : (cube : Set (ι → ℝ)) = Set.pi Set.univ (fun _ => Icc (0 : ℝ) 1) := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]

omit [DecidableEq ι] in
@[simp] theorem volume_cube : volume (cube : Set (ι → ℝ)) = 1 := by
  rw [cube_eq_pi, volume_pi_pi]
  simp

@[simp] theorem volume_cell (i : ι) : volume (cell i) = 1 := by
  rw [cell_eq_image_cube]
  have hmap : extrusionMap i = (fun y : ι → ℝ => Pi.single i 1 + y) ∘ shear i := by
    funext s
    exact extrusionMap_eq i s
  rw [hmap, Set.image_comp]
  rw [image_add_left, measure_preimage_add]
  rw [Measure.addHaar_image_linearMap, shear_det, volume_cube]
  simp

end DiagonalZonotope

end

end OAI


