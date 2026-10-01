-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapE8TailParameters
-- name    : CK_GeneralCK_PureGapE8TailParameters
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T05:16:34.158119+00:00
-- url     : https://prove2.me/theorems/fd1f67f7-46e8-4d93-9451-547ab772a7fe
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapE8TailParameters` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapE8TailParameters` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapE8TailParameters` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapE8TailParameters (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapE8TailParameters.lean)

import Definitions.Def_CK_GeneralCK_PureGapE8SmallSTailConsumer
import Definitions.Def_CK_GeneralCK_RadialConcavity

-- ===== source module GeneralCK.PureGapE8TailParameters =====
section

/-! Uniform elementary parameters for the actual E8 inverse above slope 20. -/

namespace GeneralCK

open Set Certificates.Mixed Certificates.Mixed.Tails

noncomputable def e8TailE (v : ℝ) : ℝ := -Real.log (1 - v) / v
noncomputable def e8TailW (v : ℝ) : ℝ := 1 / (2 * kap v)

theorem e8TailE_bounds {v : ℝ} (hv : 0 < v) (hv1 : v < 1) :
    1 ≤ e8TailE v ∧ e8TailE v ≤ 1 / (1 - v) := by
  have hlo := Real.log_le_sub_one_of_pos (show 0 < 1 - v by linarith)
  have hhi := neg_log_complement_le hv hv1
  constructor
  · apply (le_div_iff₀ hv).2
    linarith
  · apply (div_le_iff₀ hv).2
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hhi

theorem e8Theta_contact_logit_bounds {x : ℝ} (hx : 0 < x) :
    let v := radialContact (2 * x) 1
    logit v ≤ e8Theta x * Real.log 2 ∧
      e8Theta x * Real.log 2 ≤ logit v + 2 := by
  let v := radialContact (2 * x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) (by norm_num)
  have hk : 0 < kap v := Certificates.Mixed.kap_pos hv hvh
  have hhn : 0 ≤ hn v := hn_nonneg hv.le (by linarith)
  have hr : 0 ≤ 1 - 2 * v := by linarith
  have hc : 0 < 1 - v := by linarith
  have hJ : J v * Real.log 2 = logit v := by
    unfold J logit
    rw [Real.log_div (by linarith : 1 - v ≠ 0) hv.ne']
    field_simp
  have hθ : e8Theta x * Real.log 2 =
      logit v + (1 - 2 * v) * hn v / (2 * v * (1 - v) * kap v) := by
    unfold e8Theta
    rw [deriv_F_radius_slope (by positivity) (by norm_num)]
    change radialSlope v * Real.log 2 = _
    unfold radialSlope
    rw [add_mul, hJ]
    field_simp [log_two_pos.ne']
  change logit v ≤ e8Theta x * Real.log 2 ∧ _
  rw [hθ]
  constructor
  · have hp : 0 ≤ (1 - 2 * v) * hn v / (2 * v * (1 - v) * kap v) := by positivity
    linarith
  · have hp := hn_le_four_mul_kap hv hvh
    have hnup : (1 - 2 * v) * hn v ≤ 4 * v * (1 - v) * kap v := by
      have hm := mul_le_mul_of_nonneg_right (show 1 - 2 * v ≤ 1 by linarith) hhn
      nlinarith
    have hfrac : (1 - 2 * v) * hn v / (2 * v * (1 - v) * kap v) ≤ 2 := by
      apply (div_le_iff₀ (by positivity : 0 < 2 * v * (1 - v) * kap v)).2
      nlinarith
    linarith

theorem e8_tail_contact_small {x : ℝ} (hx : 0 < x) (hy : 20 ≤ e8Theta x) :
    radialContact (2 * x) 1 ≤ 1 / 4096 := by
  let v := radialContact (2 * x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) (by norm_num)
  have hb := e8Theta_contact_logit_bounds hx
  change logit v ≤ e8Theta x * Real.log 2 ∧ e8Theta x * Real.log 2 ≤ logit v + 2 at hb
  have hlo : (69 / 100 : ℝ) ≤ Real.log 2 := log_two_gt_69.le
  have hlog : 59 / 5 ≤ logit v := by nlinarith
  change v ≤ 1 / 4096
  by_contra hn
  have hvlo : 1 / 4096 < v := lt_of_not_ge hn
  have hratio : (1 - v) / v ≤ (4096 : ℝ) := by
    apply (div_le_iff₀ hv).2
    linarith
  have hl := Real.log_le_log (show 0 < (1 - v) / v from div_pos (by linarith) hv) hratio
  have h4096 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    norm_num
  have hhi := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hhi
  rw [h4096] at hl
  change Real.log ((1 - v) / v) ≤ 12 * Real.log 2 at hl
  change 59 / 5 ≤ Real.log ((1 - v) / v) at hlog
  linarith

theorem hn_eq_tail_parameters {v : ℝ} (hv : 0 < v) (hvh : v < 1 / 2) :
    hn v = 2 * v * kap v * (1 + (1 - 2 * v) * e8TailE v * e8TailW v) := by
  have hc : 1 - v ≠ 0 := by linarith
  have hk : kap v ≠ 0 := (Certificates.Mixed.kap_pos hv hvh).ne'
  unfold e8TailW e8TailE
  field_simp [hv.ne', hk]
  unfold hn kap
  rw [Real.log_mul hv.ne' hc]
  ring

theorem e8Theta_contact_tail_formula {x : ℝ} (hx : 0 < x) :
    let v := radialContact (2 * x) 1
    e8Theta x * Real.log 2 = logit v + (1 - 2 * v) / (1 - v) *
      (1 + (1 - 2 * v) * e8TailE v * e8TailW v) := by
  let v := radialContact (2 * x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) (by norm_num)
  have hk : kap v ≠ 0 := (Certificates.Mixed.kap_pos hv hvh).ne'
  have hc : 1 - v ≠ 0 := by linarith
  have hJ : J v * Real.log 2 = logit v := by
    unfold J logit
    rw [Real.log_div hc hv.ne']
    field_simp
  change e8Theta x * Real.log 2 = logit v + (1 - 2 * v) / (1 - v) *
    (1 + (1 - 2 * v) * e8TailE v * e8TailW v)
  unfold e8Theta
  rw [deriv_F_radius_slope (by positivity) (by norm_num)]
  change radialSlope v * Real.log 2 = _
  unfold radialSlope
  rw [add_mul, hJ, hn_eq_tail_parameters hv hvh]
  field_simp [hv.ne', hc, hk, log_two_pos.ne']

theorem e8_tail_parameter_bounds {x : ℝ} (hx : 0 < x) (hy : 20 ≤ e8Theta x) :
    let v := radialContact (2 * x) 1
    0 < v ∧ v ≤ 1 / 4096 ∧ 1 ≤ e8TailE v ∧ e8TailE v ≤ 4096 / 4095 ∧
      0 < e8TailW v ∧ e8TailW v ≤ 2 / 25 := by
  let v := radialContact (2 * x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvh : v < 1 / 2 := radialContact_lt_half (by positivity) (by norm_num)
  have hsmall : v ≤ 1 / 4096 := e8_tail_contact_small hx hy
  have he := e8TailE_bounds hv (by linarith)
  have heU : e8TailE v ≤ 4096 / 4095 := by
    apply he.2.trans
    exact (div_le_iff₀ (by linarith : 0 < 1 - v)).2 (by linarith)
  have hlo : (69 / 100 : ℝ) ≤ Real.log 2 := log_two_gt_69.le
  have hθ := e8Theta_contact_logit_bounds hx
  change logit v ≤ e8Theta x * Real.log 2 ∧ e8Theta x * Real.log 2 ≤ logit v + 2 at hθ
  have hlog : 59 / 5 ≤ logit v := by nlinarith
  have hkap : logit v / 2 ≤ kap v := by
    rw [kap_logit hv (by linarith)]
    have hh := Real.log_nonpos (show 0 ≤ 1 - v by linarith) (show 1 - v ≤ 1 by linarith)
    linarith
  have hkp : 0 < kap v := Certificates.Mixed.kap_pos hv hvh
  have hw0 : 0 < e8TailW v := by unfold e8TailW; positivity
  have hwU : e8TailW v ≤ 5 / 59 := by
    apply (div_le_iff₀ (show 0 < 2 * kap v by positivity)).2
    linarith
  have hr0 : 0 ≤ 1 - 2 * v := by linarith
  have hew := mul_le_mul heU hwU hw0.le (by norm_num : (0 : ℝ) ≤ 4096 / 4095)
  have hrew := mul_le_mul_of_nonneg_right (show 1 - 2 * v ≤ 1 by linarith)
    (mul_nonneg (by linarith : 0 ≤ e8TailE v) hw0.le)
  have hrewU : (1 - 2 * v) * e8TailE v * e8TailW v ≤ 1 / 5 := by nlinarith
  have hratio : (1 - 2 * v) / (1 - v) ≤ 1 :=
    (div_le_one (by linarith : 0 < 1 - v)).2 (by linarith)
  have hfactor : 0 ≤ 1 + (1 - 2 * v) * e8TailE v * e8TailW v := by
    have : 0 ≤ (1 - 2 * v) * e8TailE v * e8TailW v :=
      mul_nonneg (mul_nonneg hr0 (by linarith [he.1])) hw0.le
    linarith
  have hextra := mul_le_mul_of_nonneg_right hratio hfactor
  have hformula := e8Theta_contact_tail_formula hx
  change e8Theta x * Real.log 2 = logit v + (1 - 2 * v) / (1 - v) *
    (1 + (1 - 2 * v) * e8TailE v * e8TailW v) at hformula
  have hlog' : 63 / 5 ≤ logit v := by nlinarith
  refine ⟨hv, hsmall, he.1, heU, hw0, ?_⟩
  apply (div_le_iff₀ (show 0 < 2 * kap v by positivity)).2
  linarith

theorem hn_le_one_four_hundred {v : ℝ} (hv : 0 ≤ v) (hvU : v ≤ 1 / 4096) :
    hn v ≤ 1 / 400 := by
  have hm := H_strictMonoOn.monotoneOn ⟨hv, by linarith⟩
    (show (1 / 4096 : ℝ) ∈ Icc 0 (1 / 2) by norm_num) hvU
  have hm' := mul_le_mul_of_nonneg_right hm log_two_pos.le
  rw [← hn_eq_H_mul_log, ← hn_eq_H_mul_log] at hm'
  apply hm'.trans
  have hc := neg_log_complement_le (v := (1 / 4096 : ℝ)) (by norm_num) (by norm_num)
  have hp := mul_le_mul_of_nonneg_left hc (show (0 : ℝ) ≤ 1 - 1 / 4096 by norm_num)
  have hlog : Real.log (1 / 4096 : ℝ) = -12 * Real.log 2 := by
    rw [show (1 / 4096 : ℝ) = (2 ^ 12)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    norm_num
  have hhi := Certificates.PilotData.log_two.2
  norm_num only [div_one] at hhi
  unfold hn
  rw [hlog]
  norm_num at hp
  nlinarith

theorem e8_tail_inverse_value {y : ℝ} (hy : y ∈ e8SlopeRange) (hy20 : 20 ≤ y) :
    100 ≤ e8RegularQ y := by
  let x := e8Q y
  have hx : 0 < x := e8Q_pos hy
  have hθ : 20 ≤ e8Theta x := by simpa only [x, e8Theta_e8Q hy] using hy20
  let v := radialContact (2 * x) 1
  have hv : 0 < v := radialContact_pos (by positivity) (by norm_num)
  have hvU : v ≤ 1 / 4096 := e8_tail_contact_small hx hθ
  have hhn := hn_le_one_four_hundred hv.le hvU
  have he := radialContact_equation (z := 2 * x) (h := 1) (by positivity) (by norm_num)
  have he' : 2 * x * hn v = (1 - 2 * v) * Real.log 2 := by
    rw [hn_eq_H_mul_log]
    nlinarith [congrArg (fun z => z * Real.log 2) he]
  have hlo := mul_le_mul_of_nonneg_left log_two_gt_69.le
    (show 0 ≤ 1 - 2 * v by linarith)
  have hupper := mul_le_mul_of_nonneg_left hhn (show 0 ≤ 2 * x by positivity)
  rw [e8RegularQ_eq_e8Q (e8SlopeRange_subset_pos hy).le]
  change 100 ≤ x
  nlinarith

#print axioms e8TailE_bounds
#print axioms e8Theta_contact_logit_bounds
#print axioms e8_tail_contact_small
#print axioms hn_eq_tail_parameters
#print axioms e8Theta_contact_tail_formula
#print axioms e8_tail_parameter_bounds
#print axioms hn_le_one_four_hundred
#print axioms e8_tail_inverse_value

end GeneralCK

end


