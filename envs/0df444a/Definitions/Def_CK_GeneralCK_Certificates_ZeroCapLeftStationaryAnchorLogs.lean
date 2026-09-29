-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ZeroCapLeftStationaryAnchorLogs
-- name    : CK_GeneralCK_Certificates_ZeroCapLeftStationaryAnchorLogs
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:02.848459+00:00
-- url     : https://prove2.me/theorems/facc42a8-fd84-4569-8711-db85c1ae4a9e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ZeroCapLeftStationaryAnchorLogs.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

-- ===== source module GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs =====
section

/-! Eight exact 20-term log-series witnesses for the zero-cap stationary anchors.
This additive source is pending a direct Lean compile and named axiom audit. -/

namespace GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs

theorem theta1_A_reduced :
    (235975530129 / 1000000000000 : ℝ) ≤ Real.log (5000 / 3949) ∧
    Real.log (5000 / 3949 : ℝ) ≤ (23597553013 / 100000000000 : ℝ) := by
  have h := checkLog_sound (w := (1051 / 8949)) (n := 20)
    (lo := (235975530129 / 1000000000000))
    (hi := (23597553013 / 100000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem theta1_B_reduced :
    (502361545353 / 1000000000000 : ℝ) ≤ Real.log (10000 / 6051) ∧
    Real.log (10000 / 6051 : ℝ) ≤ (251180772677 / 500000000000 : ℝ) := by
  have h := checkLog_sound (w := (3949 / 16051)) (n := 20)
    (lo := (502361545353 / 1000000000000))
    (hi := (251180772677 / 500000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem theta2_A_reduced :
    (8832179157 / 200000000000 : ℝ) ≤ Real.log (625 / 598) ∧
    Real.log (625 / 598 : ℝ) ≤ (22080447893 / 500000000000 : ℝ) := by
  have h := checkLog_sound (w := (27 / 1223)) (n := 20)
    (lo := (8832179157 / 200000000000))
    (hi := (22080447893 / 500000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem theta2_B_reduced :
    (1093539071 / 4000000000 : ℝ) ≤ Real.log (1250 / 951) ∧
    Real.log (1250 / 951 : ℝ) ≤ (273384767751 / 1000000000000 : ℝ) := by
  have h := checkLog_sound (w := (299 / 2201)) (n := 20)
    (lo := (1093539071 / 4000000000))
    (hi := (273384767751 / 1000000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem theta3_A_reduced :
    (262124322049 / 500000000000 : ℝ) ≤ Real.log (125 / 74) ∧
    Real.log (125 / 74 : ℝ) ≤ (524248644099 / 1000000000000 : ℝ) := by
  have h := checkLog_sound (w := (51 / 199)) (n := 20)
    (lo := (262124322049 / 500000000000))
    (hi := (524248644099 / 1000000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem theta3_B_reduced :
    (20021094019 / 125000000000 : ℝ) ≤ Real.log (250 / 213) ∧
    Real.log (250 / 213 : ℝ) ≤ (160168752153 / 1000000000000 : ℝ) := by
  have h := checkLog_sound (w := (37 / 463)) (n := 20)
    (lo := (20021094019 / 125000000000))
    (hi := (160168752153 / 1000000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem entropy_Bmax_A_reduced :
    (677642994023 / 1000000000000 : ℝ) ≤ Real.log (128 / 65) ∧
    Real.log (128 / 65 : ℝ) ≤ (84705374253 / 125000000000 : ℝ) := by
  have h := checkLog_sound (w := (63 / 193)) (n := 20)
    (lo := (677642994023 / 1000000000000))
    (hi := (84705374253 / 125000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem entropy_Bmax_B_reduced :
    (5430641217 / 40000000000 : ℝ) ≤ Real.log (512 / 447) ∧
    Real.log (512 / 447 : ℝ) ≤ (67883015213 / 500000000000 : ℝ) := by
  have h := checkLog_sound (w := (65 / 959)) (n := 20)
    (lo := (5430641217 / 40000000000))
    (hi := (67883015213 / 500000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

#print axioms theta1_A_reduced
#print axioms theta1_B_reduced
#print axioms theta2_A_reduced
#print axioms theta2_B_reduced
#print axioms theta3_A_reduced
#print axioms theta3_B_reduced
#print axioms entropy_Bmax_A_reduced
#print axioms entropy_Bmax_B_reduced

end GeneralCK.Certificates.ZeroCapLeftStationaryAnchorLogs

end


