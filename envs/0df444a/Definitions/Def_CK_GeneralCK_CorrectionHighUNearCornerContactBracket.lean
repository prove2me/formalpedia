-- Prove2me | Definitions.Def_CK_GeneralCK_CorrectionHighUNearCornerContactBracket
-- name    : CK_GeneralCK_CorrectionHighUNearCornerContactBracket
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:48:45.772573+00:00
-- url     : https://prove2.me/theorems/e7397a22-8117-4c65-ad94-4570813fcf6c
-- title:
--   Courtade–Kumar proof module `GeneralCK.CorrectionHighUNearCornerContactBracket` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.CorrectionHighUNearCornerContactBracket` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.CorrectionHighUNearCornerContactBracket` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.CorrectionHighUNearCornerContactBracket (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/CorrectionHighUNearCornerContactBracket.lean)

import Definitions.Def_CK_GeneralCK_CorrectionHighUScaledContract
import Definitions.Def_CK_GeneralCK_EntropyParabola
import Definitions.Def_CK_GeneralCK_ReflectionRegularContact

/-!
# Rational enclosure for the actual correction contact near u=1/2

This bound uses the proved entropy parabola and the exact contact equation;
it does not assume any Hessian-minor positivity.
-/

namespace GeneralCK.Correction.HighU

open Certificates.Reflection

theorem nearCorner_contact_lt_one_thousand_one
    {t rho : ℝ} (ht : 0 < t) (ht1 : t ≤ 1 / 100)
    (hr : 0 < rho) (hr1 : rho ≤ 1 / 100) :
    0 < Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) ∧
      Natural.contact (1 / 2 - t) (1 / 2 - (1 - rho) * t) <
        (1001 / 1000 : ℝ) * rho * t := by
  let u : ℝ := 1 / 2 - t
  let w : ℝ := 1 / 2 - (1 - rho) * t
  let c : ℝ := Natural.contact u w
  have hu49 : (49 / 100 : ℝ) ≤ u := by dsimp [u]; linarith
  have hu0 : 0 < u := by linarith
  have hu1 : u < 1 / 2 := by dsimp [u]; linarith
  have hrho1 : 0 < 1 - rho := by linarith
  have hw1 : w < 1 / 2 := by
    dsimp [w]
    have hp := mul_pos hrho1 ht
    linarith
  have hdelta : w - u = rho * t := by dsimp [u, w]; ring
  have huw : u < w := by rw [← sub_pos, hdelta]; exact mul_pos hr ht
  have hw0 : 0 < w := hu0.trans huw
  have hpar := H_gt_parabola hu0 hu1
  have hquad : (2499 / 2500 : ℝ) ≤ 4 * u * (1 - u) := by
    have hp : 0 ≤ (u - 49 / 100) * (51 / 100 - u) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith only [hp]
  have hHu : (2499 / 2500 : ℝ) < H u := hquad.trans_lt hpar
  have hHw : H u ≤ H w :=
    H_strictMonoOn.monotoneOn
      ⟨hu0.le, hu1.le⟩ ⟨hw0.le, hw1.le⟩ huw.le
  have hS : 2 * Real.log 2 * H u ≤ Natural.entropySum u w := by
    have hm := mul_le_mul_of_nonneg_right hHw log_two_pos.le
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    nlinarith only [hm]
  have hS0 : 0 < Natural.entropySum u w := by
    have hHu0 : 0 < H u := by linarith
    have hHw0 : 0 < H w := hHu0.trans_le hHw
    unfold Natural.entropySum
    rw [Certificates.Mixed.hn_eq_H_mul_log, Certificates.Mixed.hn_eq_H_mul_log]
    positivity
  have hcSpec := Natural.contact_spec hu0 huw hw1
  have hc0 : 0 < c := hcSpec.1
  have hc1 : c < 1 := hcSpec.2.1
  have hEc0 : 0 < biasE c :=
    Reflection.biasE_pos_wide (by linarith) hc1
  have hEcLe : biasE c ≤ Real.log 2 :=
    Reflection.biasE_le_log_two_wide (by linarith) hc1
  have hcCross : c * Natural.entropySum u w =
      2 * (w - u) * biasE c := by
    exact (div_eq_div_iff hEc0.ne' hS0.ne').mp hcSpec.2.2
  rw [hdelta] at hcCross
  have hnum : 2 * (rho * t) * biasE c ≤
      2 * (rho * t) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hEcLe (by positivity)
  have hden : c * (2 * Real.log 2 * H u) ≤
      c * Natural.entropySum u w :=
    mul_le_mul_of_nonneg_left hS hc0.le
  have hcoarse : c * (2 * Real.log 2 * H u) ≤
      2 * (rho * t) * Real.log 2 := by
    exact hden.trans (hcCross.le.trans hnum)
  have hcoarse' : (c * H u) * (2 * Real.log 2) ≤
      (rho * t) * (2 * Real.log 2) := by
    nlinarith only [hcoarse]
  have hcoarse'' : (2 * Real.log 2) * (c * H u) ≤
      (2 * Real.log 2) * (rho * t) := by
    nlinarith only [hcoarse']
  have hbound : c * H u ≤ rho * t :=
    (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * Real.log 2)).mp hcoarse''
  have hscaled : c * (2499 / 2500 : ℝ) < rho * t :=
    (mul_lt_mul_of_pos_left hHu hc0).trans_le hbound
  have hfinal : c < (1001 / 1000 : ℝ) * rho * t := by
    have hrt : 0 < rho * t := mul_pos hr ht
    nlinarith only [hscaled, hrt]
  exact ⟨hc0, hfinal⟩

#print axioms nearCorner_contact_lt_one_thousand_one

end GeneralCK.Correction.HighU


