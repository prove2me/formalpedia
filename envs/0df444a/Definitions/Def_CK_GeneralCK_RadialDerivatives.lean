-- Prove2me | Definitions.Def_CK_GeneralCK_RadialDerivatives
-- name    : CK_GeneralCK_RadialDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:26:40.104428+00:00
-- url     : https://prove2.me/theorems/e63462da-e0ac-4745-965d-e43d814e2840
-- title:
--   Courtade–Kumar proof module `GeneralCK.RadialDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.RadialDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.RadialDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.RadialDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/RadialDerivatives.lean)

import Definitions.Def_CK_GeneralCK_RadialContact
import Definitions.Def_CK_GeneralCK_ProfileDerivatives
import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2

namespace GeneralCK
open Set Filter
open scoped Topology

theorem radialContact_image_radius {h : ℝ} (hh : 0 < h) :
    (fun z => radialContact z h) '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  · intro hv
    have hH : 0 < H v := H_pos hv.1 (by linarith [hv.2])
    have hz : 0 < h * (1 - 2 * v) / H v :=
      div_pos (mul_pos hh (by linarith [hv.2])) hH
    refine ⟨h * (1 - 2 * v) / H v, hz, ?_⟩
    apply radialContact_eq_of_equation hz hh hv.1 hv.2
    exact div_mul_cancel₀ _ hH.ne'

theorem continuousAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    ContinuousAt (fun r => radialContact r h) z := by
  have hanti : StrictAntiOn (fun r => radialContact r h) (Ioi 0) :=
    fun a ha b _ hab => radialContact_strictAnti_radius ha hab hh
  apply hanti.dual_right.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hz)
  change (fun r => radialContact r h) '' Ioi 0 ∈ 𝓝 (radialContact z h)
  rw [radialContact_image_radius hh]
  exact Ioo_mem_nhds (radialContact_pos hz hh) (radialContact_lt_half hz hh)

theorem radialContact_denominator_pos {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    0 < z * J (radialContact z h) + 2 * h := by
  have hJ := J_pos (radialContact_pos hz hh) (radialContact_lt_half hz hh)
  positivity

theorem hasDerivAt_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => radialContact r h)
      (-H (radialContact z h) / (z * J (radialContact z h) + 2 * h)) z := by
  let v := radialContact z h
  have hv : 0 < v := radialContact_pos hz hh
  have hv' : v < 1 / 2 := radialContact_lt_half hz hh
  have hH : H v ≠ 0 := (H_pos hv (by linarith)).ne'
  have heq : h * (1 - 2 * v) = z * H v := (radialContact_equation hz hh).symm
  have hd : HasDerivAt (fun u => h * (1 - 2 * u) / H u)
      (-(z * J v + 2 * h) / H v) v := by
    have hd := ((((hasDerivAt_id v).const_mul 2).const_sub 1).const_mul h).div
      (Comparison.hasDerivAt_H hv (by linarith)) hH
    convert! hd using 1
    simp only [id_eq, mul_one, heq]
    field_simp
    ring
  have hD : z * J v + 2 * h ≠ 0 := (radialContact_denominator_pos hz hh).ne'
  have hinv := hd.of_local_left_inverse (continuousAt_radialContact_radius hz hh)
    (div_ne_zero (neg_ne_zero.mpr hD) hH) (by
      filter_upwards [Ioi_mem_nhds hz] with r hr
      have hp := H_pos (radialContact_pos hr hh)
        (show radialContact r h < 1 by linarith [radialContact_lt_half hr hh])
      rw [← radialContact_equation hr hh]
      exact mul_div_cancel_right₀ r hp.ne')
  convert! hinv using 1
  change -H v / (z * J v + 2 * h) = (-(z * J v + 2 * h) / H v)⁻¹
  rw [inv_div, div_neg, neg_div]

theorem deriv_radialContact_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => radialContact r h) z =
      -H (radialContact z h) / (z * J (radialContact z h) + 2 * h) :=
  (hasDerivAt_radialContact_radius hz hh).deriv

theorem hasDerivAt_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h)
      (J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h))) z := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hd := (hasDerivAt_id z).mul
    ((hasDerivAt_J hv hv').comp z (hasDerivAt_radialContact_radius hz hh))
  have heq : (fun r => F r h) =ᶠ[𝓝 z] (fun r => r * J (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    simp only [F, ne_of_gt (show 0 < r from hr), ↓reduceIte]
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [id_eq, one_mul, Function.comp_apply, div_eq_mul_inv, mul_inv_rev]
  ring

theorem deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z =
      J (radialContact z h) + z * H (radialContact z h) /
        (Real.log 2 * radialContact z h * (1 - radialContact z h) *
          (z * J (radialContact z h) + 2 * h)) :=
  (hasDerivAt_F_radius hz hh).deriv

namespace Certificates.Mixed

theorem hn_eq_H_mul_log (v : ℝ) : hn v = H v * Real.log 2 := by
  unfold hn H Real.binEntropy
  simp only [Real.log_inv]
  rw [div_mul_cancel₀ _ log_two_pos.ne']
  ring

theorem kap_identity {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    2 * kap v = 2 * hn v + (1 - 2 * v) * (Real.log 2 * J v) := by
  unfold kap hn J
  rw [Real.log_mul hv.ne' (by linarith), Real.log_div (by linarith) hv.ne']
  field_simp
  ring

theorem kap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) : 0 < kap v := by
  have hi := kap_identity hv (show v < 1 by linarith)
  have hhn : 0 < hn v := by
    rw [hn_eq_H_mul_log]
    exact mul_pos (H_pos hv (by linarith)) log_two_pos
  have hj := J_pos hv hv'
  have hr : 0 < (1 - 2 * v) * (Real.log 2 * J v) :=
    mul_pos (by linarith) (mul_pos log_two_pos hj)
  linarith

theorem hasDerivAt_hn {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt hn (J v * Real.log 2) v := by
  simpa only [← hn_eq_H_mul_log] using
    (Comparison.hasDerivAt_H hv hv').mul_const (Real.log 2)

theorem hasDerivAt_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt kap (-(1 - 2 * v) / (2 * v * (1 - v))) v := by
  have hd := (((hasDerivAt_id v).mul ((hasDerivAt_id v).const_sub 1)).log
    (mul_ne_zero hv.ne' (by simpa using (show 1 - v ≠ 0 by linarith)))).neg.div_const 2
  convert! hd using 1
  simp only [id_eq, one_mul, Pi.mul_apply]
  field_simp
  ring

end Certificates.Mixed

open Certificates.Mixed




theorem hasDerivAt_radialSlope {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    HasDerivAt radialSlope
      (-hn v * (2 * kap v - (1 - 2 * v)^2) /
        (4 * Real.log 2 * v^2 * (1 - v)^2 * (kap v)^2)) v := by
  have hv1 : v < 1 := by linarith
  have hL : Real.log 2 ≠ 0 := log_two_pos.ne'
  have hvc : 1 - v ≠ 0 := by linarith
  have hr : 1 - 2 * v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hv').ne'
  have hJ : J v = (2 * kap v - 2 * hn v) / ((1 - 2 * v) * Real.log 2) := by
    apply (eq_div_iff (mul_ne_zero hr hL)).2
    nlinarith [kap_identity hv hv1]
  have hdN := (((hasDerivAt_id v).const_mul 2).const_sub 1).mul (hasDerivAt_hn hv hv1)
  have hdD := (((hasDerivAt_id v).const_mul (2 * Real.log 2)).mul
    ((hasDerivAt_id v).const_sub 1)).mul (hasDerivAt_kap hv hv1)
  have hd := (hasDerivAt_J hv hv1).add (hdN.div hdD (by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hL) hv.ne') hvc) hk))
  convert! hd using 1
  simp only [id_eq, mul_one, Pi.mul_apply]
  rw [hJ]
  field_simp
  ring

theorem radialContact_denominator_identity {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    (z * J (radialContact z h) + 2 * h) * (1 - 2 * radialContact z h) * Real.log 2 =
      2 * z * kap (radialContact z h) := by
  have hv := radialContact_pos hz hh
  have hv' : radialContact z h < 1 := by linarith [radialContact_lt_half hz hh]
  have hk := kap_identity hv hv'
  rw [hn_eq_H_mul_log] at hk
  have heq := radialContact_equation hz hh
  linear_combination -z * hk - (2 * Real.log 2) * heq

theorem hasDerivAt_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (fun r => F r h) (radialSlope (radialContact z h)) z := by
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  convert! hasDerivAt_F_radius hz hh using 1
  unfold radialSlope
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  field_simp [show J (radialContact z h) * z + 2 * h ≠ 0 by
    simpa only [mul_comm] using hD]
  linear_combination H (radialContact z h) * hi

theorem deriv_F_radius_slope {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    deriv (fun r => F r h) z = radialSlope (radialContact z h) :=
  (hasDerivAt_F_radius_slope hz hh).deriv

theorem hasDerivAt_deriv_F_radius {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    HasDerivAt (deriv (fun r => F r h))
      (hn (radialContact z h) * (2 * kap (radialContact z h) -
          (1 - 2 * radialContact z h)^2) * H (radialContact z h) /
        (4 * Real.log 2 * (radialContact z h)^2 * (1 - radialContact z h)^2 *
          (kap (radialContact z h))^2 * (z * J (radialContact z h) + 2 * h))) z := by
  have hd := (hasDerivAt_radialSlope (radialContact_pos hz hh)
    (radialContact_lt_half hz hh)).comp z (hasDerivAt_radialContact_radius hz hh)
  have heq : deriv (fun r => F r h) =ᶠ[𝓝 z] (fun r => radialSlope (radialContact r h)) := by
    filter_upwards [Ioi_mem_nhds hz] with r hr
    exact deriv_F_radius_slope hr hh
  have hd' := hd.congr_of_eventuallyEq heq
  convert! hd' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem radius_mul_deriv2_F_eq_profile {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    z * deriv (deriv (fun r => F r h)) z = profile (radialContact z h) := by
  rw [(hasDerivAt_deriv_F_radius hz hh).deriv]
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hD := (radialContact_denominator_pos hz hh).ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1 - radialContact z h ≠ 0 := by linarith
  have hL := log_two_pos.ne'
  have hi := radialContact_denominator_identity hz hh
  unfold profile
  rw [hn_eq_H_mul_log]
  field_simp [hD, hK, hvc, hL, hv.ne']
  linear_combination -2 * (H (radialContact z h))^2 *
    (2 * kap (radialContact z h) - (1 - 2 * radialContact z h)^2) * hi

end GeneralCK


