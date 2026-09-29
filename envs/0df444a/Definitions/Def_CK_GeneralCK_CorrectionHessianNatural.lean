-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHessianNatural
-- name    : CK_GeneralCK_CorrectionHessianNatural
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:03:49.48851+00:00
-- url     : https://prove2.me/theorems/3d595425-0a43-4611-9806-8bb040973d18
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHessianNatural` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHessianNatural` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHessianNatural` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHessianNatural (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHessianNatural.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHessianFactored
import Definitions.Def_CK_GeneralCK_ReflectionContactInverse
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK.Correction.Natural
open Certificates.Mixed Certificates.Reflection Reflection

theorem biasE_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasE (1-2*v) = hn v := by
  rw [biasE_eq_log_mul_E (by linarith) (by linarith), hn_eq_H_mul_log]
  unfold Reflection.E
  rw [show (1-(1-2*v))/2=v by ring]
  ring

theorem biasB_probability {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    biasB (1-2*v) = kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  unfold biasB kap
  rw [show 1-(1-2*v)*(1-2*v)=2^2*(v*(1-v)) by ring,
    Real.log_mul (by norm_num : (2:ℝ)^2 ≠ 0) hp.ne',Real.log_pow]
  ring

theorem A_probability (v : ℝ) :
    2*SmallMean.A (1-2*v) = Real.log 2*J v := by
  unfold SmallMean.A J
  rw [show (1+(1-2*v))/(1-(1-2*v))=(1-v)/v by ring]
  field_simp










theorem Fs_probability (v : ℝ) (hv : 0 < v) (hv' : v < 1) :
    Fs (1-2*v) = Real.log 2*radialSlope v := by
  unfold Fs
  rw [A_probability, biasE_probability hv hv', biasB_probability hv hv']
  unfold radialSlope
  rw [show (1-(1-2*v)^2)/4=v*(1-v) by ring]
  field_simp

theorem Fs_contact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Fs (1-2*radialContact z h) = Real.log 2*deriv (fun r => F r h) z := by
  rw [deriv_F_radius_slope hz hh]
  exact Fs_probability _ (radialContact_pos hz hh)
    (lt_trans (radialContact_lt_half hz hh) (by norm_num))

theorem Fss_contact {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    Fss (1-2*radialContact z h) (2*Real.log 2*h) =
      Real.log 2*deriv (deriv (fun r => F r h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1/2 := radialContact_lt_half hz hh
  have hk := (kap_pos hv hv').ne'
  have hv1 : v < 1 := by linarith
  have hnv : 1-v ≠ 0 := by linarith
  have heq : z*hn v = h*(1-2*v)*Real.log 2 := by
    rw [hn_eq_H_mul_log]
    linear_combination Real.log 2 * radialContact_equation hz hh
  have hd := radius_mul_deriv2_F_eq_profile hz hh
  change z * _ = profile v at hd
  rw [mul_comm z, ← eq_div_iff hz.ne'] at hd
  rw [hd]
  change Fss (1-2*v) (2*Real.log 2*h) = _
  unfold Fss
  rw [biasE_probability hv hv1, biasB_probability hv hv1]
  unfold profile
  rw [show (1-(1-2*v)^2)/4=v*(1-v) by ring]
  field_simp [hk, hv.ne', hnv, hz.ne', hh.ne', log_two_pos.ne']
  linear_combination 16*(hn v)^2*(2*kap v-(1-2*v)^2)*heq




















theorem jn_inverse (e : ℝ) : jn (entropyInverse e) = naturalJ e := by
  unfold jn naturalJ J
  field_simp

theorem entropySum_inverse {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    entropySum (entropyInverse e) (entropyInverse f) = 2*Real.log 2*mid e f := by
  unfold entropySum
  rw [hn_eq_H_mul_log,hn_eq_H_mul_log,
    (entropyInverse_spec he.le (hef.trans hf).le).2.2,
    (entropyInverse_spec (he.trans hef).le hf.le).2.2]
  unfold mid
  ring

theorem contact_inverse {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    contact (entropyInverse e) (entropyInverse f) = 1-2*radialContact (gap e f) (mid e f) := by
  unfold contact
  rw [entropySum_inverse he hef hf]
  unfold biasContact
  rw [radialContact_normalize_radius (gap_pos he hef hf).ne']
  congr 2
  unfold gap
  field_simp

theorem kernel_components {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    au (entropyInverse e) (entropyInverse f) = Aleft e f ∧
    nw (entropyInverse e) (entropyInverse f) = rightNumerator e f ∧
    zu (entropyInverse e) (entropyInverse f) = Zleft e f ∧
    zw (entropyInverse e) (entropyInverse f) = Zright e f ∧
    weight (entropyInverse e) (entropyInverse f) = rankWeight e f := by
  have hg := gap_pos he hef hf
  have hm := mid_pos he hef
  have hnorm : 0 < normalized e f := div_pos hg hm
  have hfs : Fs (contact (entropyInverse e) (entropyInverse f)) =
      Real.log 2*deriv (fun r => F r 1) (normalized e f) := by
    rw [contact_inverse he hef hf,
      radialContact_normalize_entropy (gap e f) hm.ne']
    exact Fs_contact hnorm (by norm_num)
  have hss := Fss_contact hg hm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold au
    rw [jn_inverse,jn_inverse,hfs]
    unfold Aleft naturalJ qp q gap
    ring
  · unfold nw
    rw [jn_inverse,jn_inverse,hfs]
    unfold rightNumerator qp q gap
    ring
  · unfold zu
    rw [jn_inverse,entropySum_inverse he hef hf]
    unfold Zleft normalized naturalJ qp q gap
    field_simp
  · unfold zw
    rw [jn_inverse,entropySum_inverse he hef hf]
    unfold Zright normalized naturalJ qp q gap
    field_simp
  · unfold weight
    rw [contact_inverse he hef hf,entropySum_inverse he hef hf,hss]
    unfold rankWeight
    ring

/-- The actual left minor equals the numerical source expression. -/
theorem m11_eq_Mleft {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    m11 (entropyInverse e) (entropyInverse f) = Mleft e f := by
  obtain ⟨ha, _, hz, _, hw⟩ := kernel_components he hef hf
  unfold m11
  rw [ha,hz,hw]
  rfl

/-- The cancellation-free numerical determinant is the actual cleared determinant. -/
theorem kdet_eq_Kfactored {e f : ℝ} (he : 0 < e) (hef : e < f) (hf : f < 1) :
    kdet (entropyInverse e) (entropyInverse f) = Kfactored e f := by
  obtain ⟨ha, hn, hz, hz', hw⟩ := kernel_components he hef hf
  unfold kdet
  rw [ha,hn,hz,hz',hw,jn_inverse]
  rfl

/-- Equality to the unexpanded `M11*M22J-Jw*M12^2` used by the C++ kernel. -/
theorem kdet_eq_source (u w : ℝ) :
    kdet u w = m11 u w*(nw u w-weight u w*(zw u w)^2*jn w)-
      jn w*(-(qp u+qp w)-weight u w*zu u w*zw u w)^2 := by
  unfold kdet m11
  ring

theorem jn_eq_log_sub {u : ℝ} (hu : 0 < u) (hu' : u < 1) :
    jn u = Real.log (1-u)-Real.log u := by
  exact Real.log_div (by linarith) hu.ne'

/-- The source contact equation, including its strict probability-bias range. -/
theorem contact_spec {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    0 < contact u w ∧ contact u w < 1 ∧
      contact u w / biasE (contact u w) = 2*(w-u)/entropySum u w := by
  have hS : 0 < entropySum u w := by
    unfold entropySum
    rw [hn_eq_H_mul_log,hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu (by linarith)) log_two_pos)
      (mul_pos (H_pos (hu.trans huw) (by linarith)) log_two_pos)
  have hy : 0 < entropySum u w/(2*(w-u)) := div_pos hS (by positivity)
  have hc := biasContact_mem hy
  have hr := biasR_biasContact hy
  change biasE (contact u w)/contact u w = _ at hr
  refine ⟨hc.1, hc.2, ?_⟩
  have hi := congrArg (fun x : ℝ => x⁻¹) hr
  simpa only [inv_div] using hi

/-- Direct probability-coordinate interface for a numerical compact certificate. -/
theorem kernel_eq_actual {u w : ℝ} (hu : 0 < u) (huw : u < w) (hw : w < 1/2) :
    m11 u w = Mleft (H u) (H w) ∧
    kdet u w = Kfactored (H u) (H w) := by
  have he := H_pos hu (by linarith)
  have hef := H_strictMonoOn ⟨hu.le, (huw.trans hw).le⟩
    ⟨(hu.trans huw).le, hw.le⟩ huw
  have hf : H w < 1 := by
    have ht := H_strictMonoOn ⟨(hu.trans huw).le, hw.le⟩
      (by norm_num : (1/2 : ℝ) ∈ Set.Icc 0 (1/2)) hw
    simpa only [H_half] using ht
  have hm := m11_eq_Mleft he hef hf
  have hk := kdet_eq_Kfactored he hef hf
  rw [entropyInverse_H_lower hu.le (huw.trans hw).le,
    entropyInverse_H_lower (hu.trans huw).le hw.le] at hm hk
  exact ⟨hm,hk⟩

end GeneralCK.Correction.Natural


