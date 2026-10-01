-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailSecondDerivative
-- name    : CK_GeneralCK_PureGapE8TailSecondDerivative
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:23:35.973824+00:00
-- url     : https://prove2.me/theorems/91be06bf-16d7-42e7-b0d2-899d10e5187c
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailSecondDerivative` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailSecondDerivative` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailSecondDerivative` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailSecondDerivative (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailSecondDerivative.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailDerivatives
import Definitions.Def_CK_GeneralCK_Certificates_E8LineAnchorInverseBridge

-- ===== source module GeneralCK.PureGapE8TailSecondDerivative =====
section

namespace GeneralCK

open Set Filter Certificates.Mixed

theorem hasDerivAt_e8TailE {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    HasDerivAt e8TailE ((1 / (1-v) - e8TailE v) / v) v := by
  have hc : 1-v ≠ 0 := by linarith
  have h := ((((hasDerivAt_id v).const_sub 1).log hc).neg).div (hasDerivAt_id v) hv.ne'
  convert! h using 1
  dsimp [e8TailE]
  field_simp [hv.ne', hc]

theorem hasDerivAt_e8TailW {v : ℝ} (hv : 0 < v) (hvh : v < 1/2) :
    HasDerivAt e8TailW ((1-2*v)*(e8TailW v)^2/(v*(1-v))) v := by
  have hc : 1-v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (kap_pos hv hvh).ne'
  have h := (hasDerivAt_const v (1 : ℝ)).div
    ((hasDerivAt_kap hv (by linarith)).const_mul 2) (mul_ne_zero (by norm_num) hk)
  convert! h using 1
  dsimp [e8TailW]
  field_simp [hv.ne', hc, hk]
  ring

theorem e8Tail_profile_derivative_identity_of_w_lt_one {v : ℝ}
    (hv : 0 < v) (hvh : v < 1/2) (hwU : e8TailW v < 1) :
    deriv profile v * ((1-2*v)*v*(1+(1-2*v)*e8TailE v*e8TailW v)) =
      profile v * e8TailBeta v (e8TailE v) (e8TailW v) := by
  have hc : 1-v ≠ 0 := by linarith
  have hk0 := kap_pos hv hvh
  have hw0 : 0 ≤ e8TailW v := by unfold e8TailW; positivity
  have hr2 : (1-2*v)^2 ≤ 1 := by nlinarith only [hv, hvh]
  have hfac : 0 < 1-(1-2*v)^2*e8TailW v := by
    nlinarith only [hwU, mul_nonneg hw0 (sub_nonneg.mpr hr2)]
  have hR := ((hasDerivAt_id v).const_mul 2).const_sub 1
  have hE := hasDerivAt_e8TailE hv (by linarith)
  have hW := hasDerivAt_e8TailW hv hvh
  have hU := ((hR.mul hE).mul hW).const_add 1
  have hV := ((hR.pow 2).mul hW).const_sub 1
  have hC := ((hasDerivAt_id v).const_sub 1).pow 2
  have hp := (((hR.mul (hU.pow 2)).mul hV).div hC (pow_ne_zero 2 hc)).div_const (Real.log 2)
  let g : ℝ → ℝ := fun z => e8TailScaledProfile z (e8TailE z) (e8TailW z) / Real.log 2
  change HasDerivAt g _ v at hp
  have heq : profile =ᶠ[nhds v] g := by
    filter_upwards [Ioo_mem_nhds hv hvh] with z hz
    exact profile_eq_e8TailScaledProfile hz.1 hz.2
  have hd := hp.congr_of_eventuallyEq heq
  rw [hd.deriv, profile_eq_e8TailScaledProfile hv hvh]
  dsimp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.add_apply, id_eq]
  unfold e8TailBeta e8TailErrorP e8TailErrorT e8TailScaledProfile
  field_simp [hv.ne', hc, hfac.ne', log_two_pos.ne']
  ring

theorem e8Tail_profile_derivative_identity {v : ℝ}
    (hv : 0 < v) (hvh : v < 1/2) (hwU : e8TailW v ≤ 2/25) :
    deriv profile v * ((1-2*v)*v*(1+(1-2*v)*e8TailE v*e8TailW v)) =
      profile v * e8TailBeta v (e8TailE v) (e8TailW v) :=
  e8Tail_profile_derivative_identity_of_w_lt_one hv hvh (by linarith)

theorem e8_theta_second_formula_of_tail_w {x : ℝ} (hx : 0 < x)
    (hw : e8TailW (radialContact (2*x) 1) < 1) :
    let v := radialContact (2*x) 1
    deriv (deriv e8Theta) x =
      -(profile v * (1 + e8TailBeta v (e8TailE v) (e8TailW v))) / x^2 := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hk : kap v ≠ 0 := (kap_pos hv hvh).ne'
  have hD : (2*x)*J v + 2 ≠ 0 := by
    have h := radialContact_denominator_pos (z := 2*x) (h := 1) (by positivity) (by norm_num)
    simpa only [mul_one, v] using h.ne'
  have hid := radialContact_denominator_identity (z := 2*x) (h := 1) (by positivity) (by norm_num)
  change ((2*x)*J v+2*1)*(1-2*v)*Real.log 2 = 2*(2*x)*kap v at hid
  have hD' : 1+x*J v ≠ 0 := by
    intro hzero
    apply hD
    nlinarith only [hzero]
  have hD'' : x*J v+1 ≠ 0 := by simpa only [add_comm] using hD'
  have hcoef : ((-H v / ((2*x)*J v+2))*2)*x =
      -((1-2*v)*v*(1+(1-2*v)*e8TailE v*e8TailW v)) := by
    calc
      _ = -((1-2*v)*hn v/(2*kap v)) := by
        rw [hn_eq_H_mul_log]
        field_simp [hD, hD', hk]
        rw [neg_inj]
        linear_combination -(H v / 2) * hid
      _ = _ := by
        rw [hn_eq_tail_parameters hv hvh]
        field_simp [hk]
  have hbeta := e8Tail_profile_derivative_identity_of_w_lt_one hv hvh hw
  have hnum : (((deriv profile v * (-H v / ((2*x)*J v+2)))*2)*x) =
      -(profile v * e8TailBeta v (e8TailE v) (e8TailW v)) := by
    calc
      _ = deriv profile v * (((-H v / ((2*x)*J v+2))*2)*x) := by ring
      _ = _ := by rw [hcoef]; nlinarith only [hbeta]
  rw [(hasDerivAt_deriv_e8Theta hx).deriv]
  change ((((deriv profile v * (-H v / ((2*x)*J v+2)))*2)*x - profile v) / x^2) = _
  rw [hnum]
  ring

theorem e8_tail_theta_second_formula {x : ℝ} (hx : 0 < x) (hy : 20 ≤ e8Theta x) :
    let v := radialContact (2*x) 1
    deriv (deriv e8Theta) x =
      -(profile v * (1 + e8TailBeta v (e8TailE v) (e8TailW v))) / x^2 :=
  e8_theta_second_formula_of_tail_w hx (by
    have hw := (e8_tail_parameter_bounds hx hy).2.2.2.2.2
    linarith)

theorem e8RegularQ_second_eq_tail {y : ℝ} (hy : y ∈ e8SlopeRange) (hy20 : 20 ≤ y) :
    let v := radialContact (2 * e8Q y) 1
    deriv (deriv e8RegularQ) y =
      (1 + e8TailBeta v (e8TailE v) (e8TailW v)) * e8Q y / (profile v)^2 := by
  have hx := e8Q_pos hy
  have hθ : 20 ≤ e8Theta (e8Q y) := by simpa only [e8Theta_e8Q hy] using hy20
  have hp := e8_tail_profile_bounds hx hθ
  have hpne : profile (radialContact (2 * e8Q y) 1) ≠ 0 := by linarith only [hp.1]
  have heq : e8RegularQ =ᶠ[nhds y] e8Q := by
    filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
    exact e8RegularQ_eq_e8Q hz.le
  rw [heq.deriv.deriv_eq,
    Certificates.E8LineAnchorInverseBridge.deriv2_e8Q_eq_secondJet_unconditional hy]
  change -deriv (deriv e8Theta) (e8Q y) / (deriv e8Theta (e8Q y))^3 = _
  rw [e8_tail_theta_second_formula hx hθ, deriv_e8Theta_eq_profile hx]
  field_simp [hx.ne', hpne]

theorem e8_tail_inverse_second_bounds {y : ℝ} (hy : y ∈ e8SlopeRange) (hy20 : 20 ≤ y) :
    2 / 5 * e8RegularQ y ≤ deriv (deriv e8RegularQ) y ∧
      deriv (deriv e8RegularQ) y ≤ 1 / 2 * e8RegularQ y := by
  have hx := e8Q_pos hy
  have hθ : 20 ≤ e8Theta (e8Q y) := by simpa only [e8Theta_e8Q hy] using hy20
  obtain ⟨hv0, hvU, he0, heU, hw0, hwU⟩ := e8_tail_parameter_bounds hx hθ
  have hb := e8Tail_beta_bounds hv0.le hvU he0 heU hw0.le hwU
  have hp := e8_tail_profile_bounds hx hθ
  have hp0 : 0 < profile (radialContact (2 * e8Q y) 1) := by linarith only [hp.1]
  have hp2l := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 57/40) hp.1 2
  have hp2u := pow_le_pow_left₀ hp0.le hp.2 2
  have hp2xl := mul_le_mul_of_nonneg_left hp2l hx.le
  have hp2xu := mul_le_mul_of_nonneg_left hp2u hx.le
  have hbxl := mul_le_mul_of_nonneg_right hb.1 hx.le
  have hbxu := mul_le_mul_of_nonneg_right hb.2 hx.le
  rw [e8RegularQ_second_eq_tail hy hy20,
    e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith only [hp2xu, hbxl, hx]
  · apply (div_le_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith only [hp2xl, hbxu, hx]

theorem e8_smallSTail_shape_bounds : E8SmallSTailShapeBounds where
  value := fun _ hy hy20 => e8_tail_inverse_value hy hy20
  first := fun _ hy hy20 => e8_tail_inverse_first_bounds hy hy20
  second := fun _ hy hy20 => e8_tail_inverse_second_bounds hy hy20

theorem e8_smallSTail_derivative_bound : E8SmallSTailDerivativeBound :=
  e8_smallSTail_derivative_of_shape_bounds e8_smallSTail_shape_bounds

theorem e8_smallSTail_unconditional :
    E8PositiveOn (fun s t => 20 ≤ t ∧ s ≤ 1/200) :=
  e8_smallSTail_of_shape_bounds e8_smallSTail_shape_bounds

#print axioms hasDerivAt_e8TailE
#print axioms hasDerivAt_e8TailW
#print axioms e8Tail_profile_derivative_identity_of_w_lt_one
#print axioms e8Tail_profile_derivative_identity
#print axioms e8_theta_second_formula_of_tail_w
#print axioms e8_tail_theta_second_formula
#print axioms e8RegularQ_second_eq_tail
#print axioms e8_tail_inverse_second_bounds
#print axioms e8_smallSTail_shape_bounds
#print axioms e8_smallSTail_derivative_bound
#print axioms e8_smallSTail_unconditional

end GeneralCK

end


