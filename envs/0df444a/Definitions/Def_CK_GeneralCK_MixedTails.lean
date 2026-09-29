-- Prove2me | Definitions.Def_CK_GeneralCK_MixedTails
-- name    : CK_GeneralCK_MixedTails
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:26:34.452263+00:00
-- url     : https://prove2.me/theorems/6a67b1e5-594d-420b-8139-50b86af4f289
-- title:
--   Courtade–Kumar proof module `GeneralCK.MixedTails` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.MixedTails` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.MixedTails` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.MixedTails (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/MixedTails.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds
import Definitions.Def_CK_GeneralCK_Certificates_MixedConstants
import Definitions.Def_CK_GeneralCK_ProfileDerivatives

namespace GeneralCK.Certificates.Mixed.Tails
open Set

theorem hn_eq_binEntropy (v : ℝ) : hn v = Real.binEntropy v := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp [hn, Real.negMulLog]
  ring

theorem hn_nonneg {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1) : 0 ≤ hn v := by
  rw [hn_eq_binEntropy]
  exact Real.binEntropy_nonneg hv hv'

theorem hasDerivAt_hn {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt hn (Real.log (1-v) - Real.log v) v := by
  rw [funext hn_eq_binEntropy]
  exact Real.hasDerivAt_binEntropy (ne_of_gt hv) (by linarith)

theorem hasDerivAt_kap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt kap (-(1-2*v)/(2*v*(1-v))) v := by
  have hd := ((((hasDerivAt_id v).mul ((hasDerivAt_id v).const_sub 1)).log
    (by change v*(1-v) ≠ 0; exact ne_of_gt (mul_pos hv (by linarith)))).neg).div_const 2
  convert! hd using 1
  dsimp
  field_simp [ne_of_gt hv, show 1-v ≠ 0 by linarith]
  ring

theorem kap_pos {v : ℝ} (hv : 0 < v) (hv' : v < 1) : 0 < kap v := by
  have hp : 0 < v*(1-v) := mul_pos hv (by linarith)
  have hp' : v*(1-v) < 1 := by nlinarith [sq_nonneg v]
  have hl := Real.log_neg hp hp'
  unfold kap
  linarith

noncomputable def entropyGap (v : ℝ) : ℝ :=
  (Real.log (1-v) - Real.log v)/2 - (1-2*v)*kap v

theorem hasDerivAt_entropyGap {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    HasDerivAt entropyGap (2*kap v-2) v := by
  have hl := (((hasDerivAt_id v).const_sub 1).log (by change 1-v ≠ 0; linarith)).sub
    ((hasDerivAt_id v).log (ne_of_gt hv))
  have hd := (hl.div_const 2).sub
    ((((hasDerivAt_id v).const_mul 2).const_sub 1).mul (hasDerivAt_kap hv hv'))
  convert! hd using 1
  dsimp
  field_simp [ne_of_gt hv, show 1-v ≠ 0 by linarith]
  ring

theorem kap_le_one_right {v : ℝ} (hv : 1/3 ≤ v) (hv' : v ≤ 1/2) : kap v ≤ 1 := by
  have hp : (1/6 : ℝ) ≤ v*(1-v) := by nlinarith
  have hl := Real.log_le_log (by norm_num : (0:ℝ) < 1/6) hp
  have hl6 : Real.log (6:ℝ) ≤ 2 := by
    have h15 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3/2)
    have h2 := PilotData.log_two.2
    norm_num only [div_one] at h2
    have he : Real.log (6:ℝ) = 2*Real.log 2 + Real.log (3/2) := by
      rw [show (6:ℝ) = 2^2*(3/2) by norm_num, log_scaled _ 2 (by norm_num)]
      norm_num
    rw [he]
    linarith
  rw [log_inv_eq] at hl
  unfold kap
  linarith

theorem hn_le_nu_kap_right {v : ℝ} (hv : 1/3 ≤ v) (hv' : v ≤ 1/2) :
    hn v ≤ (4*v*(1-v))*kap v := by
  have ha : AntitoneOn entropyGap (Icc (1/3) (1/2)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (f' := fun x => 2*kap x-2)
    · intro x hx
      exact (hasDerivAt_entropyGap (by linarith [hx.1]) (by linarith [hx.2])).continuousAt.continuousWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact (hasDerivAt_entropyGap (by linarith [hx'.1]) (by linarith [hx'.2])).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      linarith [kap_le_one_right hx'.1 hx'.2]
  have hh : entropyGap (1/2) = 0 := by norm_num [entropyGap]
  have hg := ha ⟨hv, hv'⟩ ⟨by norm_num, le_rfl⟩ hv'
  rw [hh] at hg
  have he : (4*v*(1-v))*kap v - hn v = (1-2*v)*entropyGap v := by
    unfold entropyGap kap hn
    rw [Real.log_mul (by linarith : v ≠ 0) (by linarith : 1-v ≠ 0)]
    ring
  have hp : 0 ≤ (1-2*v)*entropyGap v := mul_nonneg (by linarith) hg
  linarith

theorem profile_le_crude_right {v : ℝ} (hv : 1/3 ≤ v) (hv' : v < 1/2) :
    profile v ≤ 4*(1-2*v)/Real.log 2 := by
  have hv0 : 0 < v := by linarith
  have hv1 : v < 1 := by linarith
  have hkp := kap_pos hv0 hv1
  have hn0 := hn_nonneg hv0.le hv1.le
  have hbound := hn_le_nu_kap_right hv hv'.le
  have hr : 0 ≤ 1-2*v := by linarith
  have hnu : 0 < 4*v*(1-v) := by positivity
  have hsquare : (hn v)^2 ≤ ((4*v*(1-v))*kap v)^2 :=
    pow_le_pow_left₀ hn0 hbound 2
  have hnum : 2*(1-2*v)*(hn v)^2*(2*kap v-(1-2*v)^2) ≤
      4*(1-2*v)*(4*v*(1-v))^2*(kap v)^3 := by
    calc
      _ ≤ 2*(1-2*v)*(hn v)^2*(2*kap v) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (1-2*v)]) (by positivity)
      _ ≤ 2*(1-2*v)*((4*v*(1-v))*kap v)^2*(2*kap v) := by gcongr
      _ = _ := by ring
  have hd : 0 < Real.log 2*(4*v*(1-v))^2*(kap v)^3 := by
    exact mul_pos (mul_pos log_two_pos (sq_pos_of_pos hnu)) (pow_pos hkp 3)
  unfold profile
  calc
    _ ≤ (4*(1-2*v)*(4*v*(1-v))^2*(kap v)^3) /
        (Real.log 2*(4*v*(1-v))^2*(kap v)^3) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ = _ := by field_simp [show 1-v ≠ 0 by linarith]

/-- Analytic right tail of the retained mixed profile certificate. -/
theorem profile_right_tail {v : ℝ} (hv : 1/3 ≤ v) (hv' : v < 1/2) :
    profile v ≤ 13/6 := by
  apply (profile_le_crude_right hv hv').trans
  apply (div_le_iff₀ log_two_pos).2
  have hlog := PilotData.log_two.1
  norm_num only [div_one] at hlog
  linarith

noncomputable def logit (v : ℝ) : ℝ := Real.log ((1-v)/v)

theorem neg_log_complement_le {v : ℝ} (_hv : 0 < v) (hv' : v < 1) :
    -Real.log (1-v) ≤ v/(1-v) := by
  have hh := Real.log_le_sub_one_of_pos (inv_pos.mpr (show 0 < 1-v by linarith))
  rw [Real.log_inv] at hh
  convert hh using 1
  field_simp [show 1-v ≠ 0 by linarith]
  ring

theorem logit_ge_three {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/22) : 3 ≤ logit v := by
  have hratio : (21:ℝ) ≤ (1-v)/v := (le_div_iff₀ hv).2 (by linarith)
  exact log_twenty_one_gt_three.le.trans (Real.log_le_log (by norm_num) hratio)

theorem hn_logit {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    hn v = v*logit v - Real.log (1-v) := by
  unfold hn logit
  rw [Real.log_div (by linarith : 1-v ≠ 0) (ne_of_gt hv)]
  ring

theorem kap_logit {v : ℝ} (hv : 0 < v) (hv' : v < 1) :
    kap v = logit v/2 - Real.log (1-v) := by
  unfold kap logit
  rw [Real.log_mul (ne_of_gt hv) (by linarith : 1-v ≠ 0),
    Real.log_div (by linarith : 1-v ≠ 0) (ne_of_gt hv)]
  ring

theorem left_parameter_bounds {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/22) :
    logit v/2 ≤ kap v ∧ kap v ≤ 59*logit v/114 ∧
      hn v ≤ v*(logit v+20/19) := by
  have hv1 : v < 1 := by linarith
  have hvc : 0 < 1-v := by linarith
  have he : 3 ≤ logit v := logit_ge_three hv hv'
  have hlc := neg_log_complement_le hv hv1
  have hcomp : 0 ≤ -Real.log (1-v) :=
    neg_nonneg.mpr (Real.log_nonpos hvc.le (by linarith))
  have hfrac : v/(1-v) ≤ (20/19)*v := by
    apply (div_le_iff₀ hvc).2
    nlinarith
  have hsmall : -Real.log (1-v) ≤ 1/19 := by
    have := hlc.trans hfrac
    linarith
  rw [kap_logit hv hv1, hn_logit hv hv1]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith [hlc.trans hfrac]

theorem left_ratio_bound {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/22) :
    hn v / ((4*v*(1-v))*kap v) ≤ (10/19)*(1+(20/19)/logit v) := by
  have hp := left_parameter_bounds hv hv'
  have he := logit_ge_three hv hv'
  have he0 : 0 < logit v := by linarith
  have hk := kap_pos hv (by linarith)
  have hc : 0 < 1-v := by linarith
  have hcoef : 0 ≤ (10/19:ℝ)*(1+(20/19)/logit v) := by positivity
  have hden : (19/10)*v*logit v ≤ (4*v*(1-v))*kap v := by
    calc
      _ = (4*v*(19/20))*(logit v/2) := by ring
      _ ≤ _ := by gcongr <;> linarith
  apply (div_le_iff₀ (show 0 < (4*v*(1-v))*kap v by positivity)).2
  calc
    hn v ≤ v*(logit v+20/19) := hp.2.2
    _ = (10/19)*(1+(20/19)/logit v)*((19/10)*v*logit v) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hden hcoef

theorem left_factor_bound {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/22) :
    1-(1-2*v)^2/(2*kap v) ≤ 1-(4617/5900)/logit v := by
  have hp := left_parameter_bounds hv hv'
  have he := logit_ge_three hv hv'
  have he0 : 0 < logit v := by linarith
  have hk := kap_pos hv (by linarith)
  have hr : (81/100:ℝ) ≤ (1-2*v)^2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hr he0.le
  have hh : (4617/5900)/logit v ≤ (1-2*v)^2/(2*kap v) := by
    apply (div_le_div_iff₀ he0 (by positivity)).2
    nlinarith [hp.2.1]
  linarith

noncomputable def tailPolynomial (t : ℝ) : ℝ :=
  (1+(20/19)*t)^2*(1-(4617/5900)*t)

theorem tailPolynomial_le {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1/3) :
    tailPolynomial t ≤ tailPolynomial (1/3) := by
  have hm : MonotoneOn tailPolynomial (Icc 0 (1/3)) := by
    have hd (x : ℝ) : HasDerivAt tailPolynomial
        ((1+(20/19)*x)*(2*(20/19)-(4617/5900)-3*(20/19)*(4617/5900)*x)) x := by
      have hh := (((hasDerivAt_id x).const_mul (20/19)).const_add 1).pow 2 |>.mul
        (((hasDerivAt_id x).const_mul (4617/5900)).const_sub 1)
      convert! hh using 1
      dsimp
      ring
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    apply mul_nonneg
    · linarith [hx'.1]
    · linarith [hx'.2]
  exact hm ⟨ht, ht'⟩ ⟨by norm_num, le_rfl⟩ ht'

/-- Analytic logarithmic left tail of the retained mixed profile certificate. -/
theorem profile_left_tail {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1/22) :
    profile v ≤ 13/6 := by
  have hv1 : v < 1 := by linarith
  have hc : 0 < 1-v := by linarith
  have he := logit_ge_three hv hv'
  have he0 : 0 < logit v := by linarith
  have hk := kap_pos hv hv1
  have hn0 := hn_nonneg hv.le hv1.le
  have hr : 0 ≤ 1-2*v := by linarith
  have hratio := left_ratio_bound hv hv'
  have hfactor := left_factor_bound hv hv'
  have hq : 0 ≤ 1-(4617/5900)/logit v := by
    have hh : (4617/5900)/logit v ≤ 1 := (div_le_one he0).2 (by linarith)
    linarith
  have hcoeff : 4*(1-2*v)/Real.log 2 ≤ 400/69 := by
    apply (div_le_iff₀ log_two_pos).2
    have hl := log_two_gt_69
    linarith
  have hrep : profile v =
      (4*(1-2*v)/Real.log 2)*(hn v/((4*v*(1-v))*kap v))^2*
        (1-(1-2*v)^2/(2*kap v)) := by
    unfold profile
    field_simp [ne_of_gt hv, ne_of_gt hc, ne_of_gt hk, ne_of_gt log_two_pos]
    ring
  have ht : 1/logit v ≤ 1/3 := (div_le_iff₀ he0).2 (by linarith)
  calc
    profile v ≤ (4*(1-2*v)/Real.log 2)*(hn v/((4*v*(1-v))*kap v))^2*
        (1-(4617/5900)/logit v) := by
      rw [hrep]
      apply mul_le_mul_of_nonneg_left hfactor
      positivity
    _ ≤ (400/69)*((10/19)*(1+(20/19)/logit v))^2*
        (1-(4617/5900)/logit v) := by
      apply mul_le_mul_of_nonneg_right _ hq
      apply mul_le_mul hcoeff
        (pow_le_pow_left₀ (by positivity) hratio 2) (sq_nonneg _) (by norm_num)
    _ = (100/69)*(20/19)^2*tailPolynomial (1/logit v) := by unfold tailPolynomial; ring
    _ ≤ (100/69)*(20/19)^2*tailPolynomial (1/3) :=
      mul_le_mul_of_nonneg_left (tailPolynomial_le (by positivity) ht) (by norm_num)
    _ ≤ 13/6 := by norm_num [tailPolynomial]

end GeneralCK.Certificates.Mixed.Tails


