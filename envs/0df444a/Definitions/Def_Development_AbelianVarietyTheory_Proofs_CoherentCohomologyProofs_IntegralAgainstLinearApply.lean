-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IntegralAgainstLinearApply
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IntegralAgainstLinearApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:52.826778+00:00
-- url     : https://prove2.me/theorems/f73e6b3a-342d-45d9-8c21-cb7c0f9a930c
-- title:
--   Integral Against Linear Apply
-- statement:
--   Definitions and structural lemmas for Integral Against Linear Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IntegralAgainstLinearApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
namespace GlobalTheory.IntegralAgainstMeasure
variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]
theorem integrable_smul (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    Integrable (fun k => f k • p k) μ :=
  (f.continuous.smul p.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
noncomputable def integralAgainstLinear (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →ₗ[ℂ] B where
  toFun f := ∫ k, f k • p k ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_smul μ p f) (integrable_smul μ p g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul c _
theorem norm_integral_smul_le (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    ‖∫ k, f k • p k ∂μ‖ ≤ (μ.real Set.univ * ‖p‖) * ‖f‖ := by
  have h : ∀ᵐ k ∂μ, ‖f k • p k‖ ≤ ‖p‖ * ‖f‖ := Filter.Eventually.of_forall fun k => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (p.norm_coe_le_norm k) (f.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)
  calc ‖∫ k, f k • p k ∂μ‖ ≤ ‖p‖ * ‖f‖ * μ.real Set.univ := norm_integral_le_of_norm_le_const h
    _ = (μ.real Set.univ * ‖p‖) * ‖f‖ := by ring
noncomputable def integralAgainst (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →L[ℂ] B :=
  (integralAgainstLinear μ p).mkContinuous (μ.real Set.univ * ‖p‖) (norm_integral_smul_le μ p)
end GlobalTheory.IntegralAgainstMeasure


