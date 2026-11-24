-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:21:48.284623+00:00
-- url     : https://prove2.me/theorems/3167c17b-9bad-44e3-8d33-dd8de1486706
-- title:
--   Qequiv Apply
-- statement:
--   Definitions and structural lemmas for Qequiv Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/QequivApply.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnimodLocStd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section QR
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V)
def qmap (z : V) (ν : ℂ) : V →ₗ[ℂ] V := LinearMap.id - (ν • H.flip z).smulRight z
lemma qmap_apply (z : V) (ν : ℂ) (w : V) : qmap H z ν w = w - (ν * H w z) • z := by
  simp [qmap]
lemma qmap_coef {c h k : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = k) :
    c⁻¹ * h + (conj c)⁻¹ * (h - c⁻¹ * h * k) = 0 := by
  subst hc
  have hc1 : conj c ≠ 0 := by simpa using hc0
  field_simp
  ring
lemma qmap_qmap {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z (conj c)⁻¹ (qmap H z c⁻¹ w) = w := by
  rw [qmap_apply, qmap_apply]
  have e : H (w - (c⁻¹ * H w z) • z) z = H w z - c⁻¹ * H w z * H z z := by
    simp [map_sub, map_smul, mul_assoc]
  rw [e, sub_sub, ← add_smul, qmap_coef hc0 hc, zero_smul, sub_zero]
lemma qmap_qmap' {z : V} {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) (w : V) :
    qmap H z c⁻¹ (qmap H z (conj c)⁻¹ w) = w := by
  have h1 := qmap_qmap H (c := conj c) (by simpa using hc0) (by rw [Complex.conj_conj, add_comm]; exact hc) w
  rwa [Complex.conj_conj] at h1
def qequiv (z : V) {c : ℂ} (hc0 : c ≠ 0) (hc : c + conj c = H z z) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinear (qmap H z c⁻¹) (qmap H z (conj c)⁻¹)
    (LinearMap.ext fun w => qmap_qmap' H hc0 hc w) (LinearMap.ext fun w => qmap_qmap H hc0 hc w)
end QR
end PI.UnitaryGroupMassFormula.UnimodLocStd


