-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:57:58.118575+00:00
-- url     : https://prove2.me/theorems/bb8d866a-9f50-4749-982d-41b2702ee420
-- title:
--   PRiemann Extension Slices
-- statement:
--   Definitions and structural lemmas for PRiemann Extension Slices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/PRiemannExtensionSlices.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
namespace RiemannExtensionSlices
def torusFunctional {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (f : (Fin n → ℂ) → ℂ)
    (hf : Continuous fun θ => f (torusMap c (fun _ => r) θ)) : C(Cube n, ℂ) →L[ℂ] ℂ :=
  have hint : ∀ g : C(Cube n, ℂ), IntegrableOn
      (fun θ => jac r θ * g (cubeProj θ) * f (torusMap c (fun _ => r) θ))
      (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)) := fun g =>
    ContinuousOn.integrableOn_compact isCompact_Icc (Continuous.continuousOn
      (((continuous_jac r).mul (g.continuous.comp continuous_cubeProj)).mul hf))
  LinearMap.mkContinuousOfExistsBound
    { toFun := fctl c r f
      map_add' := fun g g' => by
        simp only [fctl, ContinuousMap.add_apply, mul_add, add_mul]
        exact integral_add (hint g) (hint g')
      map_smul' := fun a g => by
        simp only [fctl, ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext θ
        ring }
    (by
      obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := fun _ => 2 * π)).exists_bound_of_continuousOn
        (((continuous_jac r).mul hf).continuousOn)
      refine ⟨M * volume.real (Icc (0 : Fin n → ℝ) (fun _ => 2 * π)), fun g => ?_⟩
      refine (norm_setIntegral_le_of_norm_le_const (C := M * ‖g‖) measure_Icc_lt_top
        fun θ hθ => ?_).trans (le_of_eq (by ring))
      have h1 : ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ ≤ M := hM θ hθ
      rw [mul_comm (jac r θ), mul_assoc, norm_mul, mul_comm M]
      calc ‖g (cubeProj θ)‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖
          ≤ ‖g‖ * ‖jac r θ * f (torusMap c (fun _ => r) θ)‖ :=
            mul_le_mul_of_nonneg_right (g.norm_coe_le_norm _) (norm_nonneg _)
        _ ≤ ‖g‖ * M := mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
end RiemannExtensionSlices
end
end GroundTheory.Heights₂.Heights.Regular


