-- Prove2me | Definitions.Def_Eden_DerivativeDecomposition
-- name    : Eden_DerivativeDecomposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:16:39.308802+00:00
-- url     : https://prove2.me/theorems/4626514d-3f34-4759-ac89-5850362fc0c2
-- title:
--   Derivative Decomposition
-- statement:
--   Definitions and structural lemmas for Derivative Decomposition, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/DerivativeDecomposition.lean

import Definitions.Def_Eden_DerivativeFrames
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
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
namespace Eden
def diagonalLinear (d : PhaseSpace) : PhaseSpace →ₗ[ℝ] PhaseSpace where
  toFun v := WithLp.toLp 2 (fun i => d i * v i)
  map_add' := by intro v w; ext i; simp [mul_add]
  map_smul' := by intro r v; ext i; simp [smul_eq_mul]; ring
def derivativeFactors (c t : ℝ) (p : PhaseSpace) : PhaseSpace :=
  !₂[radialAmplitude t (radiusSq₁ p), planarAmplitude t (radiusSq₁ p),
     radialAmplitude t (radiusSq₂ p), planarAmplitude t (radiusSq₂ p), Real.exp (-c * t)]
end Eden


