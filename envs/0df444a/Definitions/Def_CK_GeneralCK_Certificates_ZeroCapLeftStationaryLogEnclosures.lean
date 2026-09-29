-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryLogEnclosures
-- name    : CK_GeneralCK_Certificates_ZeroCapLeftStationaryLogEnclosures
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T04:02:16.867621+00:00
-- url     : https://prove2.me/theorems/131bbebe-a07d-4d74-bd85-a97e06b8feb2
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ZeroCapLeftStationaryLogEnclosures.lean)

import Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryAnchorLogs

-- ===== source module GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures =====
section

/-! Outward-rounded real-log intervals transferred from the exact rational
20-term series witnesses. Pending direct Lean compilation and named audit. -/

namespace GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures
open ZeroCapLeftStationaryAnchorLogs

private theorem neg_log_from_reduced {v s lo hi : ℝ} {k : ℕ}
    (hv : 0 < v) (hs : 0 < s)
    (hscale : (2 : ℝ)^k * s = 1 / v)
    (hlog : lo ≤ Real.log s ∧ Real.log s ≤ hi) :
    (k : ℝ) * (34657359 / 50000000) + lo ≤ -Real.log v ∧
      -Real.log v ≤ (k : ℝ) * (693147181 / 1000000000) + hi := by
  have htwo := PilotData.log_two
  norm_num only [div_one] at htwo
  have he := Mixed.log_scaled s k hs
  rw [hscale, one_div, Real.log_inv] at he
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hl := mul_le_mul_of_nonneg_left htwo.1 hk
  have hu := mul_le_mul_of_nonneg_left htwo.2 hk
  constructor <;> linarith only [he, hlog.1, hlog.2, hl, hu]

theorem theta1_A :
    (92912271 / 100000000 : ℝ) ≤ -Real.log (3949 / 10000) ∧
    -Real.log (3949 / 10000 : ℝ) ≤ (116140339 / 125000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (3949 / 10000 : ℝ))
    (s := (5000 / 3949 : ℝ)) (k := 1) (by norm_num) (by norm_num)
    (by norm_num) theta1_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta1_B :
    (100472309 / 200000000 : ℝ) ≤ -Real.log (1 - (3949 / 10000 : ℝ)) ∧
    -Real.log (1 - (3949 / 10000 : ℝ)) ≤ (251180773 / 500000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (3949 / 10000 : ℝ)))
    (s := (10000 / 6051 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta1_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta2_A :
    (286091051 / 200000000 : ℝ) ≤ -Real.log (299 / 1250) ∧
    -Real.log (299 / 1250 : ℝ) ≤ (715227629 / 500000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (299 / 1250 : ℝ))
    (s := (625 / 598 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) theta2_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta2_B :
    (273384767 / 1000000000 : ℝ) ≤ -Real.log (1 - (299 / 1250 : ℝ)) ∧
    -Real.log (1 - (299 / 1250 : ℝ)) ≤ (4271637 / 15625000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (299 / 1250 : ℝ)))
    (s := (1250 / 951 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta2_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta3_A :
    (477635751 / 250000000 : ℝ) ≤ -Real.log (37 / 250) ∧
    -Real.log (37 / 250 : ℝ) ≤ (1910543007 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (37 / 250 : ℝ))
    (s := (125 / 74 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) theta3_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem theta3_B :
    (10010547 / 62500000 : ℝ) ≤ -Real.log (1 - (37 / 250 : ℝ)) ∧
    -Real.log (1 - (37 / 250 : ℝ)) ≤ (160168753 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (37 / 250 : ℝ)))
    (s := (250 / 213 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) theta3_B_reduced
  constructor <;> linarith only [h.1, h.2]

theorem entropy_Bmax_A :
    (1031968677 / 500000000 : ℝ) ≤ -Real.log (65 / 512) ∧
    -Real.log (65 / 512 : ℝ) ≤ (2063937357 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (65 / 512 : ℝ))
    (s := (128 / 65 : ℝ)) (k := 2) (by norm_num) (by norm_num)
    (by norm_num) entropy_Bmax_A_reduced
  constructor <;> linarith only [h.1, h.2]

theorem entropy_Bmax_B :
    (13576603 / 100000000 : ℝ) ≤ -Real.log (1 - (65 / 512 : ℝ)) ∧
    -Real.log (1 - (65 / 512 : ℝ)) ≤ (135766031 / 1000000000 : ℝ) := by
  have h := neg_log_from_reduced (v := (1 - (65 / 512 : ℝ)))
    (s := (512 / 447 : ℝ)) (k := 0) (by norm_num) (by norm_num)
    (by norm_num) entropy_Bmax_B_reduced
  constructor <;> linarith only [h.1, h.2]

#print axioms theta1_A
#print axioms theta1_B
#print axioms theta2_A
#print axioms theta2_B
#print axioms theta3_A
#print axioms theta3_B
#print axioms entropy_Bmax_A
#print axioms entropy_Bmax_B

end GeneralCK.Certificates.ZeroCapLeftStationaryLogEnclosures

end


