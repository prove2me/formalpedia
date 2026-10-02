-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenDerivatives
-- name    : CK_GeneralCK_PureGapE8TailSixteenDerivatives
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-02T02:06:27.55183+00:00
-- url     : https://prove2.me/theorems/0a1386fa-c393-400f-ae7f-48ef51221dd3
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailSixteenDerivatives` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailSixteenDerivatives` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailSixteenDerivatives` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailSixteenDerivatives (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailSixteenDerivatives.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenParameters
import Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenAlgebra
import Definitions.Def_CK_GeneralCK_PureGapE8TailSecondDerivative

-- ===== source module GeneralCK.PureGapE8TailSixteenDerivatives =====
section

namespace GeneralCK

open Set Filter Certificates.Mixed

theorem e8_sixteen_profile_bounds {x : ℝ} (hx : 0 < x) (hy : 16 ≤ e8Theta x) :
    57/40 ≤ profile (radialContact (2*x) 1) ∧
      profile (radialContact (2*x) 1) ≤ 79/50 := by
  obtain ⟨hv0, hvU, he0, heU, hw0, hwU⟩ := e8_sixteen_parameter_bounds hx hy
  have hp := e8Tail_scaled_profile_bounds_sixteen hv0.le hvU he0 heU hw0.le hwU
  have hvh : radialContact (2*x) 1 < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  rw [profile_eq_e8TailScaledProfile hv0 hvh]
  have hlo := log_two_gt_69.le
  have hhi := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hhi
  constructor
  · apply (le_div_iff₀ log_two_pos).2
    linarith only [hp.1, hhi]
  · apply (div_le_iff₀ log_two_pos).2
    linarith only [hp.2, hlo]

theorem e8_sixteen_inverse_first_bounds {y : ℝ} (hy : y ∈ e8SlopeRange) (hy16 : 16 ≤ y) :
    3/5*e8RegularQ y ≤ deriv e8RegularQ y ∧ deriv e8RegularQ y ≤ 3/4*e8RegularQ y := by
  have hx := e8Q_pos hy
  have hp := e8_sixteen_profile_bounds hx (by simpa only [e8Theta_e8Q hy] using hy16)
  have hp0 : 0 < profile (radialContact (2*e8Q y) 1) := by linarith only [hp.1]
  rw [e8RegularQ_deriv_eq_contact hy, e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  have hlo := mul_le_mul_of_nonneg_left hp.1 hx.le
  have hhi := mul_le_mul_of_nonneg_left hp.2 hx.le
  constructor
  · apply (le_div_iff₀ hp0).2
    nlinarith only [hhi, hx]
  · apply (div_le_iff₀ hp0).2
    nlinarith only [hlo, hx]

theorem e8RegularQ_second_eq_sixteen {y : ℝ} (hy : y ∈ e8SlopeRange) (hy16 : 16 ≤ y) :
    let v := radialContact (2*e8Q y) 1
    deriv (deriv e8RegularQ) y =
      (1+e8TailBeta v (e8TailE v) (e8TailW v))*e8Q y/(profile v)^2 := by
  have hx := e8Q_pos hy
  have hθ : 16 ≤ e8Theta (e8Q y) := by simpa only [e8Theta_e8Q hy] using hy16
  have hp := e8_sixteen_profile_bounds hx hθ
  have hpne : profile (radialContact (2*e8Q y) 1) ≠ 0 := by linarith only [hp.1]
  have hw : e8TailW (radialContact (2*e8Q y) 1) < 1 := by
    have hw := (e8_sixteen_parameter_bounds hx hθ).2.2.2.2.2
    linarith
  have heq : e8RegularQ =ᶠ[nhds y] e8Q := by
    filter_upwards [Ioi_mem_nhds (e8SlopeRange_subset_pos hy)] with z hz
    exact e8RegularQ_eq_e8Q hz.le
  rw [heq.deriv.deriv_eq,
    Certificates.E8LineAnchorInverseBridge.deriv2_e8Q_eq_secondJet_unconditional hy]
  change -deriv (deriv e8Theta) (e8Q y)/(deriv e8Theta (e8Q y))^3 = _
  rw [e8_theta_second_formula_of_tail_w hx hw, deriv_e8Theta_eq_profile hx]
  field_simp [hx.ne', hpne]

theorem e8_sixteen_inverse_second_bounds {y : ℝ} (hy : y ∈ e8SlopeRange) (hy16 : 16 ≤ y) :
    2/5*e8RegularQ y ≤ deriv (deriv e8RegularQ) y ∧
      deriv (deriv e8RegularQ) y ≤ 1/2*e8RegularQ y := by
  have hx := e8Q_pos hy
  have hθ : 16 ≤ e8Theta (e8Q y) := by simpa only [e8Theta_e8Q hy] using hy16
  obtain ⟨hv0, hvU, he0, heU, hw0, hwU⟩ := e8_sixteen_parameter_bounds hx hθ
  have hb := e8Tail_beta_bounds_sixteen hv0.le hvU he0 heU hw0.le hwU
  have hp := e8_sixteen_profile_bounds hx hθ
  have hp0 : 0 < profile (radialContact (2*e8Q y) 1) := by linarith only [hp.1]
  have hp2l := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 57/40) hp.1 2
  have hp2u := pow_le_pow_left₀ hp0.le hp.2 2
  have hp2xl := mul_le_mul_of_nonneg_left hp2l hx.le
  have hp2xu := mul_le_mul_of_nonneg_left hp2u hx.le
  have hbxl := mul_le_mul_of_nonneg_right hb.1 hx.le
  have hbxu := mul_le_mul_of_nonneg_right hb.2 hx.le
  rw [e8RegularQ_second_eq_sixteen hy hy16, e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith only [hp2xu, hbxl, hx]
  · apply (div_le_iff₀ (sq_pos_of_pos hp0)).2
    nlinarith only [hp2xl, hbxu, hx]

#print axioms e8_sixteen_profile_bounds
#print axioms e8_sixteen_inverse_first_bounds
#print axioms e8RegularQ_second_eq_sixteen
#print axioms e8_sixteen_inverse_second_bounds

end GeneralCK

end


