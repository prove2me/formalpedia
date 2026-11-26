-- Prove2me | Definitions.Def_Eden_HausdorffGeometry
-- name    : Eden_HausdorffGeometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:07:55.49824+00:00
-- url     : https://prove2.me/theorems/c6d197df-2016-4367-8427-7a9b072187af
-- title:
--   Hausdorff Geometry
-- statement:
--   Definitions and structural lemmas for Hausdorff Geometry, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/HausdorffGeometry.lean

import Definitions.Def_Eden_TorusAngles
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_diagonalLinear_apply
import Theorems.Thm_Eden_evolution_origin
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.diagonalLinear_apply
attribute [local simp] Eden.evolution_origin
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


set_option autoImplicit true
noncomputable section
open Set MeasureTheory
namespace Eden
def euclideanOpenCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, |x i| < 1}
def embedFour : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] PhaseSpace where
  toFun x := !₂[x 0, x 1, x 2, x 3, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp
def projectFour : PhaseSpace →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun p := !₂[p 0, p 1, p 2, p 3]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp
def projectTorus : PhaseSpace →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun p := !₂[p 0, p 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' r x := by ext i; fin_cases i <;> simp
def torusGraph (x : EuclideanSpace ℝ (Fin 2)) : PhaseSpace :=
  !₂[x 0, Real.sqrt (1 - x 0 ^ 2), x 1, Real.sqrt (1 - x 1 ^ 2), 0]
def torusParametrization (x : EuclideanSpace ℝ (Fin 2)) : PhaseSpace := torusPoint (x 0) (x 1)
end Eden


