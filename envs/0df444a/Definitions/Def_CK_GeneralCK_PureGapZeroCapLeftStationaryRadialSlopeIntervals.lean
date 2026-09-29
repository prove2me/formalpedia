-- Prove2me | Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryRadialSlopeIntervals
-- name    : CK_GeneralCK_PureGapZeroCapLeftStationaryRadialSlopeIntervals
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T19:05:36.013342+00:00
-- url     : https://prove2.me/theorems/9a558029-cafb-4de2-bd99-cc208518bcd4
-- title:
--   Courtade–Kumar proof module `GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/PureGapZeroCapLeftStationaryRadialSlopeIntervals.lean)

import Definitions.Def_CK_GeneralCK_PureGapZeroCapLeftStationaryAnchorContacts
import Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryLogEnclosures

-- ===== source module GeneralCK.PureGapZeroCapLeftStationaryRadialSlopeIntervals =====
section

/-! Source-only pointwise exact radial-slope interval bridge. It uses
negative-log boxes certified by the proved rational series checker. -/

namespace GeneralCK
open Certificates.ZeroCapLeftStationaryLogEnclosures
namespace ZeroCapLeftStationaryRadialSlopeIntervals

private theorem slope_log_formula {v : ℝ} (hv : 0 < v) (hv' : v < 1 / 2) :
    radialSlope v * Real.log 2 =
      (-Real.log v - -Real.log (1 - v)) +
        ((1 - 2 * v) / (v * (1 - v))) *
          ((v * (-Real.log v) + (1 - v) * (-Real.log (1 - v))) /
            (-Real.log v + -Real.log (1 - v))) := by
  let A : ℝ := -Real.log v
  let B : ℝ := -Real.log (1 - v)
  have hvone : v < 1 := by linarith
  have hvc : 0 < 1 - v := by linarith
  have hA : 0 < A := by
    dsimp [A]
    exact neg_pos.mpr (Real.log_neg hv hvone)
  have hB : 0 < B := by
    dsimp [B]
    exact neg_pos.mpr (Real.log_neg hvc (by linarith))
  have hJ : J v * Real.log 2 = A - B := by
    unfold J
    rw [div_mul_cancel₀ _ log_two_pos.ne', Real.log_div hvc.ne' hv.ne']
    dsimp [A, B]
    ring
  have hN : Certificates.Mixed.hn v = v * A + (1 - v) * B := by
    unfold Certificates.Mixed.hn
    dsimp [A, B]
    ring
  have hK : Certificates.Mixed.kap v = (A + B) / 2 := by
    unfold Certificates.Mixed.kap
    rw [Real.log_mul hv.ne' hvc.ne']
    dsimp [A, B]
    ring
  unfold radialSlope
  rw [add_mul, hJ, hN, hK]
  dsimp [A, B]
  field_simp [log_two_pos.ne', hv.ne', hvc.ne', (add_pos hA hB).ne']

private theorem slope_lower_from_boxes {v T Al Au Bl Bu Lhi : ℝ}
    (hv : 0 < v) (hv' : v < 1 / 2) (hT : 0 ≤ T)
    (hAl : 0 < Al) (hBl : 0 < Bl)
    (hAlo : Al ≤ -Real.log v) (hAhi : -Real.log v ≤ Au)
    (hBlo : Bl ≤ -Real.log (1 - v))
    (hBhi : -Real.log (1 - v) ≤ Bu)
    (hLhi : Real.log 2 ≤ Lhi)
    (hnumeric :
      T * Lhi ≤ Al - Bu +
        ((1 - 2 * v) / (v * (1 - v))) *
          ((v * Al + (1 - v) * Bl) / (Au + Bu))) :
    T ≤ radialSlope v := by
  let A : ℝ := -Real.log v
  let B : ℝ := -Real.log (1 - v)
  let N : ℝ := v * A + (1 - v) * B
  let n : ℝ := v * Al + (1 - v) * Bl
  let S : ℝ := A + B
  let su : ℝ := Au + Bu
  have hvone : 0 < 1 - v := by linarith
  have hn : 0 < n := by dsimp [n]; positivity
  have hN : n ≤ N := by
    dsimp [n, N, A, B]
    exact add_le_add (mul_le_mul_of_nonneg_left hAlo hv.le)
      (mul_le_mul_of_nonneg_left hBlo hvone.le)
  have hS : 0 < S := by dsimp [S, A, B]; linarith
  have hsu : 0 < su := by dsimp [su]; linarith
  have hSupper : S ≤ su := by dsimp [S, su, A, B]; linarith
  have hfrac : n / su ≤ N / S := by
    apply (div_le_div_iff₀ hsu hS).2
    have h1 := mul_le_mul_of_nonneg_left hSupper hn.le
    have h2 := mul_le_mul_of_nonneg_right hN hsu.le
    exact h1.trans h2
  have hC : 0 ≤ (1 - 2 * v) / (v * (1 - v)) :=
    div_nonneg (by linarith) (by positivity)
  have hpart := mul_le_mul_of_nonneg_left hfrac hC
  have hbase : Al - Bu ≤ A - B := by dsimp [A, B]; linarith
  have hscale := mul_le_mul_of_nonneg_left hLhi hT
  have hformula := slope_log_formula hv hv'
  have hmul : T * Real.log 2 ≤ radialSlope v * Real.log 2 := by
    dsimp [A, B, N, n, S, su] at *
    nlinarith only [hnumeric, hpart, hbase, hscale, hformula]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

private theorem slope_upper_from_boxes {v T Al Au Bl Bu Llo : ℝ}
    (hv : 0 < v) (hv' : v < 1 / 2) (hT : 0 ≤ T)
    (hAl : 0 < Al) (hBl : 0 < Bl)
    (hAlo : Al ≤ -Real.log v) (hAhi : -Real.log v ≤ Au)
    (hBlo : Bl ≤ -Real.log (1 - v))
    (hBhi : -Real.log (1 - v) ≤ Bu)
    (hLlo : Llo ≤ Real.log 2)
    (hnumeric :
      Au - Bl +
        ((1 - 2 * v) / (v * (1 - v))) *
          ((v * Au + (1 - v) * Bu) / (Al + Bl)) ≤ T * Llo) :
    radialSlope v ≤ T := by
  let A : ℝ := -Real.log v
  let B : ℝ := -Real.log (1 - v)
  let N : ℝ := v * A + (1 - v) * B
  let nu : ℝ := v * Au + (1 - v) * Bu
  let S : ℝ := A + B
  let sl : ℝ := Al + Bl
  have hvone : 0 < 1 - v := by linarith
  have hAu : 0 ≤ Au := by linarith
  have hBu : 0 ≤ Bu := by linarith
  have hnu : 0 ≤ nu := by
    dsimp [nu]
    exact add_nonneg (mul_nonneg hv.le hAu) (mul_nonneg hvone.le hBu)
  have hN : N ≤ nu := by
    dsimp [N, nu, A, B]
    exact add_le_add (mul_le_mul_of_nonneg_left hAhi hv.le)
      (mul_le_mul_of_nonneg_left hBhi hvone.le)
  have hS : 0 < S := by dsimp [S, A, B]; linarith
  have hsl : 0 < sl := by dsimp [sl]; linarith
  have hSlower : sl ≤ S := by dsimp [S, sl, A, B]; linarith
  have hfrac : N / S ≤ nu / sl := by
    apply (div_le_div_iff₀ hS hsl).2
    have h1 := mul_le_mul_of_nonneg_right hN hsl.le
    have h2 := mul_le_mul_of_nonneg_left hSlower hnu
    exact h1.trans h2
  have hC : 0 ≤ (1 - 2 * v) / (v * (1 - v)) :=
    div_nonneg (by linarith) (by positivity)
  have hpart := mul_le_mul_of_nonneg_left hfrac hC
  have hbase : A - B ≤ Au - Bl := by dsimp [A, B]; linarith
  have hscale := mul_le_mul_of_nonneg_left hLlo hT
  have hformula := slope_log_formula hv hv'
  have hmul : radialSlope v * Real.log 2 ≤ T * Real.log 2 := by
    dsimp [A, B, N, nu, S, sl] at *
    nlinarith only [hnumeric, hpart, hbase, hscale, hformula]
  exact (mul_le_mul_iff_right₀ log_two_pos).mp (by simpa only [mul_comm] using hmul)

theorem radialSlope1_lower :
    (121 / 100 : ℝ) ≤ radialSlope (3949 / 10000) := by
  exact slope_lower_from_boxes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) theta1_A.1 theta1_A.2 theta1_B.1 theta1_B.2
    (by have h := Certificates.PilotData.log_two.2; norm_num at h ⊢; exact h)
    (by norm_num)

theorem radialSlope2_lower :
    (3 : ℝ) ≤ radialSlope (299 / 1250) := by
  exact slope_lower_from_boxes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) theta2_A.1 theta2_A.2 theta2_B.1 theta2_B.2
    (by have h := Certificates.PilotData.log_two.2; norm_num at h ⊢; exact h)
    (by norm_num)

theorem radialSlope3_upper :
    radialSlope (37 / 250) ≤ (417 / 100 : ℝ) := by
  exact slope_upper_from_boxes (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) theta3_A.1 theta3_A.2 theta3_B.1 theta3_B.2
    (by have h := Certificates.PilotData.log_two.1; norm_num at h ⊢; exact h)
    (by norm_num)

end ZeroCapLeftStationaryRadialSlopeIntervals

#print axioms GeneralCK.ZeroCapLeftStationaryRadialSlopeIntervals.radialSlope1_lower
#print axioms GeneralCK.ZeroCapLeftStationaryRadialSlopeIntervals.radialSlope2_lower
#print axioms GeneralCK.ZeroCapLeftStationaryRadialSlopeIntervals.radialSlope3_upper

end GeneralCK

end


