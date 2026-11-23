-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RConvFExistsPfAbs
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RConvFExistsPfAbs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:00.128939+00:00
-- url     : https://prove2.me/theorems/70be67dc-00f9-452f-9a14-dd32c53a4490
-- title:
--   RConv FExists Pf Abs
-- statement:
--   Definitions and structural lemmas for RConv FExists Pf Abs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RConvFExistsPfAbs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.RConvFExistsPf
open MeasureTheory
open scoped InnerProductSpace
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem wk_integrable {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : Integrable (fun g => f g * ⟪x, U g y⟫_ℂ) μ := by
  refine (hf.norm.mul_const (‖x‖ * ‖y‖)).mono' (hf.aestronglyMeasurable.mul (hm x y))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x))) (norm_nonneg _)
theorem wk_bound {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by
  calc ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖x‖ * ‖y‖) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x)))
          (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by rw [integral_mul_const, mul_assoc]
def wkForm {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ)
      (fun x₁ x₂ y => by
        simp only [inner_add_left, mul_add]
        exact integral_add (wk_integrable hU hm hf x₁ y) (wk_integrable hU hm hf x₂ y))
      (fun c x y => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; funext g; ring)
      (fun x y₁ y₂ => by
        simp only [map_add, inner_add_right, mul_add]
        exact integral_add (wk_integrable hU hm hf x y₁) (wk_integrable hU hm hf x y₂))
      (fun c x y => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring))
    (∫ g, ‖f g‖ ∂μ) (fun x y => wk_bound hU hf x y)
end Formalism.L2.SG.Pf.RConvFExistsPf


