-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmEtaPeriodLatticeClassPf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:36.083804+00:00
-- url     : https://prove2.me/theorems/40466ccb-ad51-451f-b90e-39c819bb123c
-- title:
--   Cfun Om Eta Period Lattice Class Pf
-- statement:
--   Definitions and structural lemmas for Cfun Om Eta Period Lattice Class Pf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmEtaPeriodLatticeClassPf.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex
open scoped Real Modular MatrixGroups
namespace EtaPeriodLatticeClass
theorem discriminant_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (γ • τ) = denom γ τ ^ (12 : ℤ) * ModularForm.discriminant τ := by
  have h := congr_fun
    (SlashInvariantForm.slash_action_generators_SL2Z discriminant_S_invariant discriminant_T_invariant γ) τ
  rw [SL_slash_apply] at h
  have hd : denom γ τ ≠ 0 := denom_ne_zero γ τ
  rw [← h, mul_comm (ModularForm.discriminant (γ • τ)), ← mul_assoc, ← zpow_add₀ hd]
  simp
theorem norm_eta_smul_pow_four (γ : SL(2, ℤ)) (τ : ℍ) :
    ‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4 = ‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4 := by
  have h := congr_arg norm (discriminant_smul γ τ)
  simp only [ModularForm.discriminant, norm_mul, norm_pow, norm_zpow] at h
  have h6 : (‖η ((γ • τ : ℍ) : ℂ)‖ ^ 4) ^ 6 = (‖denom γ τ‖ ^ 2 * ‖η (τ : ℂ)‖ ^ 4) ^ 6 := by
    rw [← pow_mul, mul_pow, ← pow_mul, ← pow_mul]
    rw [show (4 : ℕ) * 6 = 24 from rfl, show (2 : ℕ) * 6 = 12 from rfl, h]
    norm_cast
  exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h6
theorem etaPeriod_smul (γ : SL(2, ℤ)) (τ : ℍ) : etaPeriod (γ • τ) = etaPeriod τ := by
  unfold etaPeriod
  rw [norm_eta_smul_pow_four, ModularGroup.im_smul_eq_div_normSq, Complex.normSq_eq_norm_sq]
  have : ‖denom γ τ‖ ≠ 0 := norm_ne_zero_iff.mpr (denom_ne_zero γ τ)
  field_simp
end EtaPeriodLatticeClass
example : etaPeriod (ModularGroup.T • UpperHalfPlane.I) = etaPeriod UpperHalfPlane.I :=
  EtaPeriodLatticeClass.etaPeriod_smul _ _
end GroundTheory.Heights₂.Theta


