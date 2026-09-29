-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerContactRemainder
-- name    : CK_GeneralCK_CorrectionHighUNearCornerContactRemainder
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:14:01.78725+00:00
-- url     : https://prove2.me/theorems/9ca1e44c-046d-4874-acf6-7b648f33dd08
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerContactRemainder` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerContactRemainder` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerContactRemainder` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerContactRemainder (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerContactRemainder.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerContactBracket

/-!
# A uniform cubic error bound for the actual near-corner contact

The physical contact is strictly larger than the coordinate gap `rho*t`,
and differs from it by less than `5*rho*t^3`.  This is an unconditional
analytic estimate, obtained from entropy monotonicity and the entropy
parabola.  It does not assert either of the raw Hessian wedge inequalities.
-/

namespace GeneralCK.Correction.HighU

open Certificates.Reflection

theorem nearCorner_contact_cubic_remainder
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    0 < Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) - rho * t ∧
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) - rho * t <
        5 * rho * t ^ 3 := by
  let u : ℝ := 1 / 2 - t
  let w : ℝ := 1 / 2 - (1 - rho) * t
  let c : ℝ := Natural.contact u w
  let d : ℝ := rho * t
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : u < 1 / 2 := by dsimp [u]; linarith
  have hd : 0 < d := mul_pos hr ht
  have hdelta : w - u = d := by dsimp [u, w, d]; ring
  have huw : u < w := by linarith
  have hw0 : 0 < w := hu0.trans huw
  have hw1 : w < 1 / 2 := by
    have hp : 0 < (1 - rho) * t := mul_pos (by linarith) ht
    dsimp [w]
    linarith
  have hcb : 0 < c ∧ c < (1001 / 1000 : ℝ) * d := by
    simpa only [c, u, w, d, mul_assoc] using
      nearCorner_contact_lt_one_thousand_one ht ht1 hr hr1
  have hc1 : c < 1 := (Natural.contact_spec hu0 huw hw1).2.1
  have hS0 : 0 < Natural.entropySum u w := by
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    exact add_pos (mul_pos (H_pos hu0 (by linarith)) log_two_pos)
      (mul_pos (H_pos hw0 (by linarith)) log_two_pos)
  have hEc0 : 0 < biasE c :=
    Reflection.biasE_pos_wide (by linarith [hcb.1]) hc1
  have hEq : c * Natural.entropySum u w = 2 * d * biasE c := by
    have h := (div_eq_div_iff hEc0.ne' hS0.ne').mp
      (Natural.contact_spec hu0 huw hw1).2.2
    change c * Natural.entropySum u w = 2 * (w - u) * biasE c at h
    simpa only [hdelta] using h
  have hHuw : H u < H w := H_strictMonoOn
    ⟨hu0.le, hu1.le⟩ ⟨hw0.le, hw1.le⟩ huw
  have hSupper : Natural.entropySum u w < 2 * biasE c := by
    let v : ℝ := (1 - c) / 2
    have hdt : d ≤ t / 100 := by dsimp [d]; nlinarith only [mul_le_mul_of_nonneg_right hr1 ht.le]
    have hwv : w < v := by dsimp [w, v]; nlinarith only [hcb.2, hdt, ht, hr1]
    have hv0 : 0 < v := hw0.trans hwv
    have hv1 : v < 1 / 2 := by dsimp [v]; linarith [hcb.1]
    have hHwv : H w < H v := H_strictMonoOn
      ⟨hw0.le, hw1.le⟩ ⟨hv0.le, hv1.le⟩ hwv
    have hE : biasE c = H v * Real.log 2 := by
      rw [show c = 1 - 2 * v by dsimp [v]; ring,
        Natural.biasE_probability hv0 (by linarith), Certificates.Mixed.hn_eq_H_mul_log]
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log, hE]
    nlinarith only [mul_lt_mul_of_pos_right hHuw log_two_pos,
      mul_lt_mul_of_pos_right hHwv log_two_pos]
  have hdc : d < c := by
    have hp := mul_lt_mul_of_pos_left hSupper hd
    apply (mul_lt_mul_iff_left₀ hS0).mp
    nlinarith only [hp, hEq]
  have hpar : 1 - 4 * t ^ 2 < H u := by
    have hp := H_gt_parabola hu0 hu1
    dsimp [u] at hp ⊢
    nlinarith only [hp]
  have hSlower : 2 * Real.log 2 * H u ≤ Natural.entropySum u w := by
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    nlinarith only [mul_le_mul_of_nonneg_right hHuw.le log_two_pos.le]
  have hEle : biasE c ≤ Real.log 2 :=
    Reflection.biasE_le_log_two_wide (by linarith [hcb.1]) hc1
  have hcoarse : c * H u ≤ d := by
    have hl := mul_le_mul_of_nonneg_left hSlower hcb.1.le
    have hu := mul_le_mul_of_nonneg_left hEle (show 0 ≤ 2 * d by positivity)
    apply (mul_le_mul_iff_left₀ (show 0 < 2 * Real.log 2 by positivity)).mp
    nlinarith only [hl, hu, hEq]
  have hpoly : c * (1 - 4 * t ^ 2) < d :=
    (mul_lt_mul_of_pos_left hpar hcb.1).trans_le hcoarse
  change 0 < c - d ∧ c - d < 5 * rho * t ^ 3
  refine ⟨sub_pos.mpr hdc, ?_⟩
  calc
    c - d < 4 * c * t ^ 2 := by nlinarith only [hpoly]
    _ ≤ 4 * ((1001 / 1000 : ℝ) * d) * t ^ 2 := by
      gcongr
      exact hcb.2.le
    _ ≤ 5 * d * t ^ 2 := by nlinarith only [mul_nonneg hd.le (sq_nonneg t)]
    _ = 5 * rho * t ^ 3 := by dsimp [d]; ring

/-- The normalized contact has a uniform error of order `t^2`, independent
of how quickly the positive ratio coordinate approaches zero. -/
theorem nearCorner_contact_ratio_remainder
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    0 < Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) / (rho * t) - 1 ∧
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) / (rho * t) - 1 <
        5 * t ^ 2 := by
  obtain ⟨hl, hu⟩ := nearCorner_contact_cubic_remainder ht ht1 hr hr1
  have hd : 0 < rho * t := mul_pos hr ht
  constructor
  · have hh : rho * t < Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) :=
      sub_pos.mp hl
    have := (lt_div_iff₀ hd).2 (by simpa using hh : 1 * (rho * t) < _)
    linarith
  · have hh := (div_lt_iff₀ hd).2
      (show Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) <
        (5 * t ^ 2 + 1) * (rho * t) by nlinarith only [hu])
    linarith

#print axioms nearCorner_contact_cubic_remainder
#print axioms nearCorner_contact_ratio_remainder

end GeneralCK.Correction.HighU


