-- Prove2me | Definitions.Def_CK_GeneralCK_EntropyCurvatureReduction
-- name    : CK_GeneralCK_EntropyCurvatureReduction
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:40:39.314989+00:00
-- url     : https://prove2.me/theorems/b7cac202-7bd9-4b0a-b630-9c0655bf0eaa
-- title:
--   Courtade–Kumar proof module `GeneralCK.EntropyCurvatureReduction` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.EntropyCurvatureReduction` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.EntropyCurvatureReduction` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.EntropyCurvatureReduction (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EntropyCurvatureReduction.lean)

import Definitions.Def_CK_GeneralCK_EntropyCurvatureDefs

namespace GeneralCK.EntropyCurvature
open Set Filter
open scoped Topology
open Certificates.Mixed

theorem hn_eq_kap_sub {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    hn v = kap v-(1-2*v)*xi v := by
  have hh := kap_identity hv hv'
  unfold xi
  linarith

set_option maxHeartbeats 1600000 in
theorem hasDerivAt_beta {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    HasDerivAt beta (-4*(1-2*v)*R v/((kap v)^4*(4*v*(1-v))^3)) v := by
  have hv1 : v < 1 := by linarith
  have hvc : 1-v ≠ 0 := by linarith
  have hK := (kap_pos hv hv').ne'
  have hr := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hnu := ((hasDerivAt_id v).const_mul 4).mul ((hasDerivAt_id v).const_sub 1)
  have hkap := hasDerivAt_kap hv hv1
  have hnum := (((hasDerivAt_hn hv hv1).const_mul 2).mul (hr.pow 2)).mul
    ((hkap.const_mul 2).sub (hr.pow 2))
  have hden := (hkap.pow 3).mul (hnu.pow 2)
  have hd := hnum.div hden (by
    change (kap v)^3*(4*v*(1-v))^2 ≠ 0
    exact mul_ne_zero (pow_ne_zero _ hK) (pow_ne_zero _ (by positivity)))
  convert! hd using 1
  dsimp [R, polyR, xi]
  rw [hn_eq_kap_sub hv hv1]
  unfold xi
  field_simp [hK, hv.ne', hvc]
  ring

theorem beta_antitoneOn_of_R
    (hR : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 ≤ R v) : AntitoneOn beta (Ioo 0 (1/2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo _ _)
    (f' := fun v => -4*(1-2*v)*R v/((kap v)^4*(4*v*(1-v))^3))
  · intro v hv
    exact (hasDerivAt_beta hv.1 hv.2).continuousAt.continuousWithinAt
  · intro v hv
    have hv' := interior_subset hv
    exact (hasDerivAt_beta hv'.1 hv'.2).hasDerivWithinAt
  · intro v hv
    have hv' := interior_subset hv
    have hv0 := hv'.1
    have hvc : 0 < 1-v := by linarith [hv'.2]
    have ht : 0 ≤ 1-2*v := by linarith [hv'.2]
    have hs := hR v hv'
    apply div_nonpos_of_nonpos_of_nonneg
    · nlinarith [mul_nonneg ht hs]
    · positivity

set_option maxHeartbeats 1600000 in
theorem scaled_curvature_difference {v : ℝ} (hv : 0 < v) (hv' : v < 1/2) :
    H v*Scalar.etaCurvature (H v)-beta v =
      2*hn v*P v/((4*v*(1-v))^2*(xi v)^3*(kap v)^3) := by
  have hJ := (J_pos hv hv').ne'
  have hK := (kap_pos hv hv').ne'
  have hvc : 1-v ≠ 0 := by linarith
  unfold Scalar.etaCurvature
  rw [entropyInverse_H_lower hv.le hv'.le]
  unfold Scalar.curvatureNumerator beta P polyP xi
  rw [hn_eq_H_mul_log]
  field_simp [log_two_pos.ne', hv.ne', hvc, hJ, hK]
  ring

theorem scaled_etaCurvature_gt_beta {h : ℝ} (h0 : 0 < h) (h1 : h < 1)
    (hP : 0 < P (entropyInverse h)) :
    beta (entropyInverse h) < h*Scalar.etaCurvature h := by
  have hv := entropyInverse_pos h0 h1.le
  have hv' := entropyInverse_lt_half h0.le h1
  have he := (entropyInverse_spec h0.le h1.le).2.2
  have hd := scaled_curvature_difference hv hv'
  rw [he] at hd
  have hn0 : 0 < hn (entropyInverse h) := by
    rw [hn_eq_H_mul_log, he]
    exact mul_pos h0 log_two_pos
  have hx : 0 < xi (entropyInverse h) := by
    unfold xi
    exact div_pos (mul_pos log_two_pos (J_pos hv hv')) (by norm_num)
  have hk := kap_pos hv hv'
  have hvc : 0 < 1-entropyInverse h := by linarith
  have hp : 0 < 2*hn (entropyInverse h)*P (entropyInverse h) /
      ((4*entropyInverse h*(1-entropyInverse h))^2*(xi (entropyInverse h))^3*
        (kap (entropyInverse h))^3) := by positivity
  linarith

theorem inverse_le_contact {z h : ℝ} (hz : 0 < z) (hz' : z < 1)
    (hh : 0 < h) (hcap : h ≤ H ((1-z)/2)) :
    entropyInverse h ≤ radialContact z h := by
  have hh1 : h ≤ 1 := hcap.trans (H_le_one _)
  have hq := entropyInverse_spec hh.le hh1
  have hm0 : 0 ≤ (1-z)/2 := by linarith
  have hm1 : (1-z)/2 ≤ 1/2 := by linarith
  have hinv := entropyInverse_mono hh.le (H_le_one _) hcap
  rw [entropyInverse_H_lower hm0 hm1] at hinv
  apply (le_radialContact_iff hz hh hq.1 hq.2.1).2
  rw [hq.2.2]
  nlinarith

set_option maxHeartbeats 1600000 in
theorem scaled_F_curvature {z h : ℝ} (hz : 0 < z) (hh : 0 < h) :
    h*deriv (deriv (F z)) h = beta (radialContact z h) := by
  have hv := radialContact_pos hz hh
  have hv' := radialContact_lt_half hz hh
  have hK := (kap_pos hv hv').ne'
  have hvc : 1-radialContact z h ≠ 0 := by linarith
  have he := radialContact_equation hz hh
  have hi := radius_mul_deriv2_F_eq_profile hz hh
  rw [deriv2_F_entropy hz hh]
  have heq : deriv (deriv (fun r => F r h)) z = profile (radialContact z h)/z :=
    (eq_div_iff hz.ne').2 (by simpa only [mul_comm] using hi)
  rw [heq]
  unfold beta profile
  rw [hn_eq_H_mul_log]
  field_simp [hz.ne', hh.ne', hK, hvc, hv.ne', log_two_pos.ne']
  linear_combination (1-2*radialContact z h)*H (radialContact z h)*
    (2*kap (radialContact z h)-(1-2*radialContact z h)^2)*he

theorem hasDerivAt_radialPhi_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) (hh' : h < 1) :
    HasDerivAt (radialPhi z) (deriv eta h-deriv (F z) h) h :=
  ((hasDerivAt_eta hh hh').differentiableAt.hasDerivAt).sub
    ((hasDerivAt_F_entropy hz hh).differentiableAt.hasDerivAt)

theorem hasDerivAt_deriv_radialPhi_entropy {z h : ℝ}
    (hz : 0 < z) (hh : 0 < h) (hh' : h < 1) :
    HasDerivAt (deriv (radialPhi z))
      (Scalar.etaCurvature h-deriv (deriv (F z)) h) h := by
  have hd := (Scalar.hasDerivAt_deriv_eta hh hh').sub
    ((hasDerivAt_deriv_F_entropy hz hh).differentiableAt.hasDerivAt)
  have heq : deriv (radialPhi z) =ᶠ[𝓝 h] (fun q => deriv eta q-deriv (F z) q) := by
    filter_upwards [Ioo_mem_nhds hh hh'] with q hq
    exact (hasDerivAt_radialPhi_entropy hz hq.1 hq.2).deriv
  exact hd.congr_of_eventuallyEq heq

theorem deriv2_radialPhi_entropy {z h : ℝ} (hz : 0 < z) (hh : 0 < h) (hh' : h < 1) :
    deriv (deriv (radialPhi z)) h = Scalar.etaCurvature h-deriv (deriv (F z)) h :=
  (hasDerivAt_deriv_radialPhi_entropy hz hh hh').deriv

theorem entropy_cap_lt_one {z : ℝ} (hz : 0 < z) (hz' : z < 1) : H ((1-z)/2) < 1 := by
  calc
    H ((1-z)/2) < H (1/2) :=
      H_strictMonoOn ⟨by linarith, by linarith⟩ ⟨by norm_num, le_rfl⟩ (by linarith)
    _ = 1 := H_half

theorem deriv2_radialPhi_entropy_pos_of_signs
    (hP : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 < P v)
    (hR : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 ≤ R v)
    {z h : ℝ} (hz : 0 < z) (hz' : z < 1) (hh : 0 < h)
    (hcap : h ≤ H ((1-z)/2)) : 0 < deriv (deriv (radialPhi z)) h := by
  have hh' : h < 1 := hcap.trans_lt (entropy_cap_lt_one hz hz')
  have hq : entropyInverse h ∈ Ioo (0:ℝ) (1/2) :=
    ⟨entropyInverse_pos hh hh'.le, entropyInverse_lt_half hh.le hh'⟩
  have hv : radialContact z h ∈ Ioo (0:ℝ) (1/2) :=
    ⟨radialContact_pos hz hh, radialContact_lt_half hz hh⟩
  have hb := beta_antitoneOn_of_R hR hq hv (inverse_le_contact hz hz' hh hcap)
  have hs := scaled_etaCurvature_gt_beta hh hh' (hP _ hq)
  rw [← scaled_F_curvature hz hh] at hb
  have hc : deriv (deriv (F z)) h < Scalar.etaCurvature h :=
    (mul_lt_mul_iff_right₀ hh).mp (hb.trans_lt hs)
  rw [deriv2_radialPhi_entropy hz hh hh']
  linarith

theorem radialPhi_zero : radialPhi 0 = eta := by
  funext h
  simp [radialPhi, F]

theorem deriv2_radialPhi_entropy_nonneg_of_signs
    (hP : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 < P v)
    (hR : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 ≤ R v)
    {z h : ℝ} (hz : 0 ≤ z) (hz' : z < 1) (hh : 0 < h) (hh' : h < 1)
    (hcap : h ≤ H ((1-z)/2)) : 0 ≤ deriv (deriv (radialPhi z)) h := by
  rcases hz.eq_or_lt with rfl | hz
  · rw [radialPhi_zero]
    exact Scalar.deriv2_eta_nonneg hh hh'
  · exact (deriv2_radialPhi_entropy_pos_of_signs hP hR hz hz' hh hcap).le

/-- Entropy convexity on the complete feasible positive-entropy interval,
conditional only on the two scalar signs. -/
theorem radialPhi_entropy_convexOn_of_signs
    (hP : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 < P v)
    (hR : ∀ v ∈ Ioo (0:ℝ) (1/2), 0 ≤ R v)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z < 1) :
    ConvexOn ℝ (Ioc 0 (H ((1-z)/2))) (radialPhi z) := by
  rcases hz.eq_or_lt with rfl | hz
  · simpa only [sub_zero, H_half, radialPhi_zero] using Scalar.eta_convexOn_Ioc
  · have hcap := entropy_cap_lt_one hz hz'
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioc _ _)
      (f' := deriv (radialPhi z))
      (f'' := fun h => Scalar.etaCurvature h-deriv (deriv (F z)) h)
    · intro h hh
      exact (hasDerivAt_radialPhi_entropy hz hh.1 (hh.2.trans_lt hcap)).continuousAt.continuousWithinAt
    · intro h hh
      have hh' := interior_subset hh
      exact ((hasDerivAt_radialPhi_entropy hz hh'.1
        (hh'.2.trans_lt hcap)).differentiableAt.hasDerivAt).hasDerivWithinAt
    · intro h hh
      have hh' := interior_subset hh
      exact (hasDerivAt_deriv_radialPhi_entropy hz hh'.1 (hh'.2.trans_lt hcap)).hasDerivWithinAt
    · intro h hh
      have hh' := interior_subset hh
      rw [← deriv2_radialPhi_entropy hz hh'.1 (hh'.2.trans_lt hcap)]
      exact (deriv2_radialPhi_entropy_pos_of_signs hP hR hz hz' hh'.1 hh'.2).le

end GeneralCK.EntropyCurvature


