-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailSixteenParameters
-- name    : CK_GeneralCK_PureGapE8TailSixteenParameters
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T11:24:07.019338+00:00
-- url     : https://prove2.me/theorems/3438f2cd-c316-4499-a81f-1f74d407a48b
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailSixteenParameters` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailSixteenParameters` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailSixteenParameters` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailSixteenParameters (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailSixteenParameters.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8TailParameters

-- ===== source module GeneralCK.PureGapE8TailSixteenParameters =====
section

namespace GeneralCK

open Set Certificates.Mixed Certificates.Mixed.Tails

theorem e8_sixteen_contact_small {x : ℝ} (hx : 0 < x) (hy : 16 ≤ e8Theta x) :
    radialContact (2*x) 1 ≤ 1/8192 := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hb := e8Theta_contact_logit_bounds hx
  change logit v ≤ e8Theta x * Real.log 2 ∧ e8Theta x * Real.log 2 ≤ logit v+2 at hb
  change v ≤ 1/8192
  by_contra hn
  have hvlo : 1/8192 < v := lt_of_not_ge hn
  have hratio : (1-v)/v ≤ (8192 : ℝ) := (div_le_iff₀ hv).2 (by linarith)
  have hl := Real.log_le_log (div_pos (show 0 < 1-v by linarith) hv) hratio
  have h8192 : Real.log (8192 : ℝ) = 13*Real.log 2 := by
    rw [show (8192 : ℝ) = 2^13 by norm_num, Real.log_pow]
    norm_num
  rw [h8192] at hl
  change logit v ≤ 13*Real.log 2 at hl
  nlinarith only [hb.2, hl, hy, log_two_gt_69]

theorem e8_sixteen_parameter_bounds {x : ℝ} (hx : 0 < x) (hy : 16 ≤ e8Theta x) :
    let v := radialContact (2*x) 1
    0 < v ∧ v ≤ 1/8192 ∧ 1 ≤ e8TailE v ∧ e8TailE v ≤ 8192/8191 ∧
      0 < e8TailW v ∧ e8TailW v ≤ 101/1000 := by
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1/2 := radialContact_lt_half (by positivity) (by norm_num)
  have hvU : v ≤ 1/8192 := e8_sixteen_contact_small hx hy
  have he := e8TailE_bounds hv (by linarith)
  have heU : e8TailE v ≤ 8192/8191 := by
    apply he.2.trans
    exact (div_le_iff₀ (by linarith : 0 < 1-v)).2 (by linarith)
  have hθ := e8Theta_contact_logit_bounds hx
  change logit v ≤ e8Theta x * Real.log 2 ∧ e8Theta x * Real.log 2 ≤ logit v+2 at hθ
  have hlog : 226/25 ≤ logit v := by nlinarith only [hθ.2, hy, log_two_gt_69]
  have hkap : logit v/2 ≤ kap v := by
    rw [kap_logit hv (by linarith)]
    have hh := Real.log_nonpos (show 0 ≤ 1-v by linarith) (show 1-v ≤ 1 by linarith)
    linarith
  have hkp : 0 < kap v := Certificates.Mixed.kap_pos hv hvh
  have hw0 : 0 < e8TailW v := by unfold e8TailW; positivity
  have hwU : e8TailW v ≤ 25/226 := by
    apply (div_le_iff₀ (show 0 < 2*kap v by positivity)).2
    linarith
  have hr0 : 0 ≤ 1-2*v := by linarith
  have hew := mul_le_mul heU hwU hw0.le (by norm_num : (0 : ℝ) ≤ 8192/8191)
  have hrew := mul_le_mul_of_nonneg_right (show 1-2*v ≤ 1 by linarith)
    (mul_nonneg (by linarith : 0 ≤ e8TailE v) hw0.le)
  have hrewU : (1-2*v)*e8TailE v*e8TailW v ≤ 1/8 := by nlinarith only [hew, hrew]
  have hratio : (1-2*v)/(1-v) ≤ 1 :=
    (div_le_one (by linarith : 0 < 1-v)).2 (by linarith)
  have hfactor : 0 ≤ 1+(1-2*v)*e8TailE v*e8TailW v := by
    have hp := mul_nonneg (mul_nonneg hr0 (show 0 ≤ e8TailE v by linarith)) hw0.le
    linarith
  have hextra := mul_le_mul_of_nonneg_right hratio hfactor
  have hformula := e8Theta_contact_tail_formula hx
  change e8Theta x*Real.log 2 = logit v+(1-2*v)/(1-v)*
    (1+(1-2*v)*e8TailE v*e8TailW v) at hformula
  have hlog' : 1983/200 ≤ logit v := by
    nlinarith only [hformula, hextra, hrewU, hy, log_two_gt_69]
  refine ⟨hv, hvU, he.1, heU, hw0, ?_⟩
  apply (div_le_iff₀ (show 0 < 2*kap v by positivity)).2
  linarith only [hkap, hlog']

theorem e8_sixteen_inverse_value {y : ℝ} (hy : y ∈ e8SlopeRange) (hy16 : 16 ≤ y) :
    100 ≤ e8RegularQ y := by
  let x := e8Q y
  have hx : 0 < x := e8Q_pos hy
  have hθ : 16 ≤ e8Theta x := by simpa only [x, e8Theta_e8Q hy] using hy16
  let v := radialContact (2*x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvU : v ≤ 1/8192 := e8_sixteen_contact_small hx hθ
  have hhn := hn_le_one_four_hundred hv.le (by linarith)
  have he := radialContact_equation (z := 2*x) (h := 1) (by positivity) (by norm_num)
  have he' : 2*x*hn v = (1-2*v)*Real.log 2 := by
    rw [hn_eq_H_mul_log]
    nlinarith only [congrArg (fun z => z*Real.log 2) he]
  have hlo := mul_le_mul_of_nonneg_left log_two_gt_69.le (show 0 ≤ 1-2*v by linarith)
  have hupper := mul_le_mul_of_nonneg_left hhn (show 0 ≤ 2*x by positivity)
  rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  change 100 ≤ x
  nlinarith only [he', hlo, hupper, hvU]

#print axioms e8_sixteen_contact_small
#print axioms e8_sixteen_parameter_bounds
#print axioms e8_sixteen_inverse_value

end GeneralCK

end


