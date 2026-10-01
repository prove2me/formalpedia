-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0000Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0000Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:31:15.609049+00:00
-- url     : https://prove2.me/theorems/27103b76-3341-4557-9a3c-eedebf4d942f
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0000Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0001Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0000Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0004Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0005Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0006Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0000Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0004Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0005Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0006Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0000Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0001Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0002Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0003Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0004Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0005Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0006Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0000Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0001Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0002Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0003Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0004Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0005Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0006Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0000Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0000
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (470003629 / 1000000000) ≤ -Real.log (5 / 8) ∧
    -Real.log (5 / 8) ≤ (47000363 / 100000000) := by
  have h := checkLog_sound (w := (3 / 13)) (n := 12)
    (lo := (470003629 / 1000000000)) (hi := (47000363 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 5) = 1/(5 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (470003629 / 1000000000) (47000363 / 100000000) (Real.log (8 / 5)) := by
  have h := reflection_log_1_neg
  have he : Real.log (8 / 5) = -Real.log (5 / 8) := by
    rw [show ((8 / 5) : ℝ) = ((5 / 8) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (916290731 / 1000000000) ≤ -Real.log (2 / 5) ∧
    -Real.log (2 / 5) ≤ (916290733 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5 / 4) = 1/(2 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-916290733 / 1000000000) (-916290731 / 1000000000) (Real.log (2 / 5)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (45580389 / 250000000) ≤ -Real.log (5 / 6) ∧
    -Real.log (5 / 6) ≤ (182321557 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 11)) (n := 12)
    (lo := (45580389 / 250000000)) (hi := (182321557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6 / 5) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6 / 5) = 1/(5 / 6) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (45580389 / 250000000) (182321557 / 1000000000) (Real.log (6 / 5)) := by
  have h := reflection_log_5_neg
  have he : Real.log (6 / 5) = -Real.log (5 / 6) := by
    rw [show ((6 / 5) : ℝ) = ((5 / 6) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (223143551 / 1000000000) ≤ -Real.log (4 / 5) ∧
    -Real.log (4 / 5) ≤ (1743309 / 7812500) := by
  have h := checkLog_sound (w := (1 / 9)) (n := 12)
    (lo := (223143551 / 1000000000)) (hi := (1743309 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 4) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5 / 4) = 1/(4 / 5) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1743309 / 7812500) (-223143551 / 1000000000) (Real.log (4 / 5)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (161268147 / 1000000000) ≤ -Real.log (40 / 47) ∧
    -Real.log (40 / 47) ≤ (40317037 / 250000000) := by
  have h := checkLog_sound (w := (7 / 87)) (n := 12)
    (lo := (161268147 / 1000000000)) (hi := (40317037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47 / 40) = 1/(40 / 47) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (161268147 / 1000000000) (40317037 / 250000000) (Real.log (47 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (47 / 40) = -Real.log (40 / 47) := by
    rw [show ((47 / 40) : ℝ) = ((40 / 47) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (48092973 / 250000000) ≤ -Real.log (33 / 40) ∧
    -Real.log (33 / 40) ≤ (192371893 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 33) = 1/(33 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-192371893 / 1000000000) (-48092973 / 250000000) (Real.log (33 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (580673089 / 1000000000) ≤ -Real.log (1000000 / 1787241) ∧
    -Real.log (1000000 / 1787241) ≤ (58067309 / 100000000) := by
  have h := checkLog_sound (w := (787241 / 2787241)) (n := 12)
    (lo := (580673089 / 1000000000)) (hi := (58067309 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1787241 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1787241 / 1000000) = 1/(1000000 / 1787241) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (580673089 / 1000000000) (58067309 / 100000000) (Real.log (1787241 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1787241 / 1000000) = -Real.log (1000000 / 1787241) := by
    rw [show ((1787241 / 1000000) : ℝ) = ((1000000 / 1787241) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193449401 / 125000000) ≤ -Real.log (212759 / 1000000) ∧
    -Real.log (212759 / 1000000) ≤ (1547595211 / 1000000000) := by
  have h := checkLog_sound (w := (37241 / 462759)) (n := 12)
    (lo := (10081303 / 62500000)) (hi := (161300849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 212759) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 212759) = 1/(212759 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1547595211 / 1000000000) (-193449401 / 125000000) (Real.log (212759 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (145479173 / 250000000) ≤ -Real.log (200000 / 357893) ∧
    -Real.log (200000 / 357893) ≤ (581916693 / 1000000000) := by
  have h := checkLog_sound (w := (157893 / 557893)) (n := 12)
    (lo := (145479173 / 250000000)) (hi := (581916693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357893 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357893 / 200000) = 1/(200000 / 357893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (145479173 / 250000000) (581916693 / 1000000000) (Real.log (357893 / 200000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (357893 / 200000) = -Real.log (200000 / 357893) := by
    rw [show ((357893 / 200000) : ℝ) = ((200000 / 357893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1558103367 / 1000000000) ≤ -Real.log (42107 / 200000) ∧
    -Real.log (42107 / 200000) ≤ (155810337 / 100000000) := by
  have h := checkLog_sound (w := (7893 / 92107)) (n := 12)
    (lo := (171809007 / 1000000000)) (hi := (10738063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42107) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(50000 / 42107) = 1/(42107 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-155810337 / 100000000) (-1558103367 / 1000000000) (Real.log (42107 / 200000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (107649127 / 200000000) ≤ -Real.log (1000000 / 1712999) ∧
    -Real.log (1000000 / 1712999) ≤ (134561409 / 250000000) := by
  have h := checkLog_sound (w := (712999 / 2712999)) (n := 12)
    (lo := (107649127 / 200000000)) (hi := (134561409 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1712999 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1712999 / 1000000) = 1/(1000000 / 1712999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (107649127 / 200000000) (134561409 / 250000000) (Real.log (1712999 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1712999 / 1000000) = -Real.log (1000000 / 1712999) := by
    rw [show ((1712999 / 1000000) : ℝ) = ((1000000 / 1712999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (624134789 / 500000000) ≤ -Real.log (287001 / 1000000) ∧
    -Real.log (287001 / 1000000) ≤ (62413479 / 50000000) := by
  have h := checkLog_sound (w := (212999 / 787001)) (n := 12)
    (lo := (277561199 / 500000000)) (hi := (555122399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 287001) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 287001) = 1/(287001 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-62413479 / 50000000) (-624134789 / 500000000) (Real.log (287001 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (21711293 / 40000000) ≤ -Real.log (250000 / 430197) ∧
    -Real.log (250000 / 430197) ≤ (271391163 / 500000000) := by
  have h := checkLog_sound (w := (180197 / 680197)) (n := 12)
    (lo := (21711293 / 40000000)) (hi := (271391163 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((430197 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(430197 / 250000) = 1/(250000 / 430197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (21711293 / 40000000) (271391163 / 500000000) (Real.log (430197 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (430197 / 250000) = -Real.log (250000 / 430197) := by
    rw [show ((430197 / 250000) : ℝ) = ((250000 / 430197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (159472991 / 125000000) ≤ -Real.log (69803 / 250000) ∧
    -Real.log (69803 / 250000) ≤ (127578393 / 100000000) := by
  have h := checkLog_sound (w := (55197 / 194803)) (n := 12)
    (lo := (145659187 / 250000000)) (hi := (582636749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 69803) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 69803) = 1/(69803 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-127578393 / 100000000) (-159472991 / 125000000) (Real.log (69803 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2128268297 / 1000000000) ≤ -Real.log (20000000000 / 168006147801) ∧
    -Real.log (20000000000 / 168006147801) ≤ (2128268301 / 1000000000) := by
  have h := checkLog_sound (w := (8006147801 / 328006147801)) (n := 12)
    (lo := (48826757 / 1000000000)) (hi := (24413379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168006147801 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(168006147801 / 160000000000) = 1/(20000000000 / 168006147801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2128268297 / 1000000000) (2128268301 / 1000000000) (Real.log (168006147801 / 20000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (168006147801 / 20000000000) = -Real.log (20000000000 / 168006147801) := by
    rw [show ((168006147801 / 20000000000) : ℝ) = ((20000000000 / 168006147801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2140020059 / 1000000000) ≤ -Real.log (500000000000 / 4249804070583) ∧
    -Real.log (500000000000 / 4249804070583) ≤ (2140020063 / 1000000000) := by
  have h := checkLog_sound (w := (249804070583 / 8249804070583)) (n := 12)
    (lo := (60578519 / 1000000000)) (hi := (1514463 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4249804070583 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4249804070583 / 4000000000000) = 1/(500000000000 / 4249804070583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2140020059 / 1000000000) (2140020063 / 1000000000) (Real.log (4249804070583 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (4249804070583 / 500000000000) = -Real.log (500000000000 / 4249804070583) := by
    rw [show ((4249804070583 / 500000000000) : ℝ) = ((500000000000 / 4249804070583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1786515213 / 1000000000) ≤ -Real.log (500000000000 / 2984308417043) ∧
    -Real.log (500000000000 / 2984308417043) ≤ (111657201 / 62500000) := by
  have h := checkLog_sound (w := (984308417043 / 4984308417043)) (n := 12)
    (lo := (400220853 / 1000000000)) (hi := (200110427 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2984308417043 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2984308417043 / 2000000000000) = 1/(500000000000 / 2984308417043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1786515213 / 1000000000) (111657201 / 62500000) (Real.log (2984308417043 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2984308417043 / 500000000000) = -Real.log (500000000000 / 2984308417043) := by
    rw [show ((2984308417043 / 500000000000) : ℝ) = ((500000000000 / 2984308417043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1818566253 / 1000000000) ≤ -Real.log (500000000000 / 3081507958111) ∧
    -Real.log (500000000000 / 3081507958111) ≤ (113660391 / 62500000) := by
  have h := checkLog_sound (w := (1081507958111 / 5081507958111)) (n := 12)
    (lo := (432271893 / 1000000000)) (hi := (216135947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3081507958111 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(3081507958111 / 2000000000000) = 1/(500000000000 / 3081507958111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1818566253 / 1000000000) (113660391 / 62500000) (Real.log (3081507958111 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (3081507958111 / 500000000000) = -Real.log (500000000000 / 3081507958111) := by
    rw [show ((3081507958111 / 500000000000) : ℝ) = ((500000000000 / 3081507958111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0000

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0001Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0001
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (462160451 / 1000000000) ≤ -Real.log (80 / 127) ∧
    -Real.log (80 / 127) ≤ (115540113 / 250000000) := by
  have h := checkLog_sound (w := (47 / 207)) (n := 12)
    (lo := (462160451 / 1000000000)) (hi := (115540113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((127 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(127 / 80) = 1/(80 / 127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (462160451 / 1000000000) (115540113 / 250000000) (Real.log (127 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (127 / 80) = -Real.log (80 / 127) := by
    rw [show ((127 / 80) : ℝ) = ((80 / 127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (27672471 / 31250000) ≤ -Real.log (33 / 80) ∧
    -Real.log (33 / 80) ≤ (442759537 / 500000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 33) = 1/(33 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-442759537 / 500000000) (-27672471 / 31250000) (Real.log (33 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (161268147 / 1000000000) ≤ -Real.log (40 / 47) ∧
    -Real.log (40 / 47) ≤ (40317037 / 250000000) := by
  have h := checkLog_sound (w := (7 / 87)) (n := 12)
    (lo := (161268147 / 1000000000)) (hi := (40317037 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47 / 40) = 1/(40 / 47) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (161268147 / 1000000000) (40317037 / 250000000) (Real.log (47 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (47 / 40) = -Real.log (40 / 47) := by
    rw [show ((47 / 40) : ℝ) = ((40 / 47) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (48092973 / 250000000) ≤ -Real.log (33 / 40) ∧
    -Real.log (33 / 40) ≤ (192371893 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 73)) (n := 12)
    (lo := (48092973 / 250000000)) (hi := (192371893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 33) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 33) = 1/(33 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-192371893 / 1000000000) (-48092973 / 250000000) (Real.log (33 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (579592069 / 1000000000) ≤ -Real.log (100000 / 178531) ∧
    -Real.log (100000 / 178531) ≤ (57959207 / 100000000) := by
  have h := checkLog_sound (w := (78531 / 278531)) (n := 12)
    (lo := (579592069 / 1000000000)) (hi := (57959207 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178531 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178531 / 100000) = 1/(100000 / 178531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (579592069 / 1000000000) (57959207 / 100000000) (Real.log (178531 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (178531 / 100000) = -Real.log (100000 / 178531) := by
    rw [show ((178531 / 100000) : ℝ) = ((100000 / 178531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (30771203 / 20000000) ≤ -Real.log (21469 / 100000) ∧
    -Real.log (21469 / 100000) ≤ (1538560153 / 1000000000) := by
  have h := checkLog_sound (w := (3531 / 46469)) (n := 12)
    (lo := (15226579 / 100000000)) (hi := (152265791 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 21469) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(25000 / 21469) = 1/(21469 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1538560153 / 1000000000) (-30771203 / 20000000) (Real.log (21469 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (580673649 / 1000000000) ≤ -Real.log (500000 / 893621) ∧
    -Real.log (500000 / 893621) ≤ (11613473 / 20000000) := by
  have h := checkLog_sound (w := (393621 / 1393621)) (n := 12)
    (lo := (580673649 / 1000000000)) (hi := (11613473 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((893621 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(893621 / 500000) = 1/(500000 / 893621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (580673649 / 1000000000) (11613473 / 20000000) (Real.log (893621 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (893621 / 500000) = -Real.log (500000 / 893621) := by
    rw [show ((893621 / 500000) : ℝ) = ((500000 / 893621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (386899977 / 250000000) ≤ -Real.log (106379 / 500000) ∧
    -Real.log (106379 / 500000) ≤ (1547599911 / 1000000000) := by
  have h := checkLog_sound (w := (18621 / 231379)) (n := 12)
    (lo := (40326387 / 250000000)) (hi := (161305549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 106379) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 106379) = 1/(106379 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1547599911 / 1000000000) (-386899977 / 250000000) (Real.log (106379 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (533701171 / 1000000000) ≤ -Real.log (62500 / 106577) ∧
    -Real.log (62500 / 106577) ≤ (133425293 / 250000000) := by
  have h := checkLog_sound (w := (44077 / 169077)) (n := 12)
    (lo := (533701171 / 1000000000)) (hi := (133425293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((106577 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(106577 / 62500) = 1/(62500 / 106577) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (533701171 / 1000000000) (133425293 / 250000000) (Real.log (106577 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (106577 / 62500) = -Real.log (62500 / 106577) := by
    rw [show ((106577 / 62500) : ℝ) = ((62500 / 106577) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (76347917 / 62500000) ≤ -Real.log (18423 / 62500) ∧
    -Real.log (18423 / 62500) ≤ (610783337 / 500000000) := by
  have h := checkLog_sound (w := (12827 / 49673)) (n := 12)
    (lo := (132104873 / 250000000)) (hi := (528419493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 18423) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 18423) = 1/(18423 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-610783337 / 500000000) (-76347917 / 62500000) (Real.log (18423 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (538246219 / 1000000000) ≤ -Real.log (1000 / 1713) ∧
    -Real.log (1000 / 1713) ≤ (26912311 / 50000000) := by
  have h := checkLog_sound (w := (713 / 2713)) (n := 12)
    (lo := (538246219 / 1000000000)) (hi := (26912311 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1713 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1713 / 1000) = 1/(1000 / 1713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (538246219 / 1000000000) (26912311 / 50000000) (Real.log (1713 / 1000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1713 / 1000) = -Real.log (1000 / 1713) := by
    rw [show ((1713 / 1000) : ℝ) = ((1000 / 1713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (624136531 / 500000000) ≤ -Real.log (287 / 1000) ∧
    -Real.log (287 / 1000) ≤ (156034133 / 125000000) := by
  have h := checkLog_sound (w := (213 / 787)) (n := 12)
    (lo := (277562941 / 500000000)) (hi := (555125883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500 / 287) = 1/(287 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-156034133 / 125000000) (-624136531 / 500000000) (Real.log (287 / 1000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2118152219 / 1000000000) ≤ -Real.log (500000000000 / 4157878801993) ∧
    -Real.log (500000000000 / 4157878801993) ≤ (2118152223 / 1000000000) := by
  have h := checkLog_sound (w := (157878801993 / 8157878801993)) (n := 12)
    (lo := (38710679 / 1000000000)) (hi := (967767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4157878801993 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4157878801993 / 4000000000000) = 1/(500000000000 / 4157878801993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2118152219 / 1000000000) (2118152223 / 1000000000) (Real.log (4157878801993 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4157878801993 / 500000000000) = -Real.log (500000000000 / 4157878801993) := by
    rw [show ((4157878801993 / 500000000000) : ℝ) = ((500000000000 / 4157878801993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2128273557 / 1000000000) ≤ -Real.log (20000000000 / 168007031463) ∧
    -Real.log (20000000000 / 168007031463) ≤ (2128273561 / 1000000000) := by
  have h := checkLog_sound (w := (8007031463 / 328007031463)) (n := 12)
    (lo := (48832017 / 1000000000)) (hi := (24416009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((168007031463 / 160000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(168007031463 / 160000000000) = 1/(20000000000 / 168007031463) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2128273557 / 1000000000) (2128273561 / 1000000000) (Real.log (168007031463 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (168007031463 / 20000000000) = -Real.log (20000000000 / 168007031463) := by
    rw [show ((168007031463 / 20000000000) : ℝ) = ((20000000000 / 168007031463) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1755267843 / 1000000000) ≤ -Real.log (5000000000 / 28924985073) ∧
    -Real.log (5000000000 / 28924985073) ≤ (877633923 / 500000000) := by
  have h := checkLog_sound (w := (8924985073 / 48924985073)) (n := 12)
    (lo := (368973483 / 1000000000)) (hi := (92243371 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((28924985073 / 20000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(28924985073 / 20000000000) = 1/(5000000000 / 28924985073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1755267843 / 1000000000) (877633923 / 500000000) (Real.log (28924985073 / 5000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (28924985073 / 5000000000) = -Real.log (5000000000 / 28924985073) := by
    rw [show ((28924985073 / 5000000000) : ℝ) = ((5000000000 / 28924985073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1786519281 / 1000000000) ≤ -Real.log (125000000000 / 746080139373) ∧
    -Real.log (125000000000 / 746080139373) ≤ (446629821 / 250000000) := by
  have h := checkLog_sound (w := (246080139373 / 1246080139373)) (n := 12)
    (lo := (400224921 / 1000000000)) (hi := (200112461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((746080139373 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(746080139373 / 500000000000) = 1/(125000000000 / 746080139373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1786519281 / 1000000000) (446629821 / 250000000) (Real.log (746080139373 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (746080139373 / 125000000000) = -Real.log (125000000000 / 746080139373) := by
    rw [show ((746080139373 / 125000000000) : ℝ) = ((125000000000 / 746080139373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0001

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0002Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0002
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (56781909 / 125000000) ≤ -Real.log (40 / 63) ∧
    -Real.log (40 / 63) ≤ (454255273 / 1000000000) := by
  have h := checkLog_sound (w := (23 / 103)) (n := 12)
    (lo := (56781909 / 125000000)) (hi := (454255273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((63 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(63 / 40) = 1/(40 / 63) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (56781909 / 125000000) (454255273 / 1000000000) (Real.log (63 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (63 / 40) = -Real.log (40 / 63) := by
    rw [show ((63 / 40) : ℝ) = ((40 / 63) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (855666109 / 1000000000) ≤ -Real.log (17 / 40) ∧
    -Real.log (17 / 40) ≤ (855666111 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 17) = 1/(17 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-855666111 / 1000000000) (-855666109 / 1000000000) (Real.log (17 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
    -Real.log (16 / 25) ≤ (446287103 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 16) = 1/(16 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (223143551 / 500000000) (446287103 / 1000000000) (Real.log (25 / 16)) := by
  have h := reflection_log_3_neg
  have he : Real.log (25 / 16) = -Real.log (16 / 25) := by
    rw [show ((25 / 16) : ℝ) = ((16 / 25) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (206669643 / 250000000) ≤ -Real.log (7 / 16) ∧
    -Real.log (7 / 16) ≤ (413339287 / 500000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8 / 7) = 1/(7 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-413339287 / 500000000) (-206669643 / 250000000) (Real.log (7 / 16)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (69880971 / 500000000) ≤ -Real.log (20 / 23) ∧
    -Real.log (20 / 23) ≤ (139761943 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 43)) (n := 12)
    (lo := (69880971 / 500000000)) (hi := (139761943 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23 / 20) = 1/(20 / 23) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (69880971 / 500000000) (139761943 / 1000000000) (Real.log (23 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (23 / 20) = -Real.log (20 / 23) := by
    rw [show ((23 / 20) : ℝ) = ((20 / 23) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (162518929 / 1000000000) ≤ -Real.log (17 / 20) ∧
    -Real.log (17 / 20) ≤ (16251893 / 100000000) := by
  have h := checkLog_sound (w := (3 / 37)) (n := 12)
    (lo := (162518929 / 1000000000)) (hi := (16251893 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 17) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 17) = 1/(17 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-16251893 / 100000000) (-162518929 / 1000000000) (Real.log (17 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (23556607 / 200000000) ≤ -Real.log (8 / 9) ∧
    -Real.log (8 / 9) ≤ (29445759 / 250000000) := by
  have h := checkLog_sound (w := (1 / 17)) (n := 12)
    (lo := (23556607 / 200000000)) (hi := (29445759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9 / 8) = 1/(8 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (23556607 / 200000000) (29445759 / 250000000) (Real.log (9 / 8)) := by
  have h := reflection_log_7_neg
  have he : Real.log (9 / 8) = -Real.log (8 / 9) := by
    rw [show ((9 / 8) : ℝ) = ((8 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (521607 / 3906250) ≤ -Real.log (7 / 8) ∧
    -Real.log (7 / 8) ≤ (133531393 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 7) = 1/(7 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-133531393 / 1000000000) (-521607 / 3906250) (Real.log (7 / 8)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (289337641 / 500000000) ≤ -Real.log (500000 / 891837) ∧
    -Real.log (500000 / 891837) ≤ (578675283 / 1000000000) := by
  have h := checkLog_sound (w := (391837 / 1391837)) (n := 12)
    (lo := (289337641 / 500000000)) (hi := (578675283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891837 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891837 / 500000) = 1/(500000 / 891837) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (289337641 / 500000000) (578675283 / 1000000000) (Real.log (891837 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (891837 / 500000) = -Real.log (500000 / 891837) := by
    rw [show ((891837 / 500000) : ℝ) = ((500000 / 891837) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (382742187 / 250000000) ≤ -Real.log (108163 / 500000) ∧
    -Real.log (108163 / 500000) ≤ (1530968751 / 1000000000) := by
  have h := checkLog_sound (w := (16837 / 233163)) (n := 12)
    (lo := (36168597 / 250000000)) (hi := (144674389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108163) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 108163) = 1/(108163 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1530968751 / 1000000000) (-382742187 / 250000000) (Real.log (108163 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (579592629 / 1000000000) ≤ -Real.log (1000000 / 1785311) ∧
    -Real.log (1000000 / 1785311) ≤ (57959263 / 100000000) := by
  have h := checkLog_sound (w := (785311 / 2785311)) (n := 12)
    (lo := (579592629 / 1000000000)) (hi := (57959263 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1785311 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1785311 / 1000000) = 1/(1000000 / 1785311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (579592629 / 1000000000) (57959263 / 100000000) (Real.log (1785311 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1785311 / 1000000) = -Real.log (1000000 / 1785311) := by
    rw [show ((1785311 / 1000000) : ℝ) = ((1000000 / 1785311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192320601 / 125000000) ≤ -Real.log (214689 / 1000000) ∧
    -Real.log (214689 / 1000000) ≤ (1538564811 / 1000000000) := by
  have h := checkLog_sound (w := (35311 / 464689)) (n := 12)
    (lo := (9516903 / 62500000)) (hi := (152270449 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 214689) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 214689) = 1/(214689 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1538564811 / 1000000000) (-192320601 / 125000000) (Real.log (214689 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (105829313 / 200000000) ≤ -Real.log (1000000 / 1697483) ∧
    -Real.log (1000000 / 1697483) ≤ (264573283 / 500000000) := by
  have h := checkLog_sound (w := (697483 / 2697483)) (n := 12)
    (lo := (105829313 / 200000000)) (hi := (264573283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697483 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1697483 / 1000000) = 1/(1000000 / 1697483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (105829313 / 200000000) (264573283 / 500000000) (Real.log (1697483 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1697483 / 1000000) = -Real.log (1000000 / 1697483) := by
    rw [show ((1697483 / 1000000) : ℝ) = ((1000000 / 1697483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (298904451 / 250000000) ≤ -Real.log (302517 / 1000000) ∧
    -Real.log (302517 / 1000000) ≤ (597808903 / 500000000) := by
  have h := checkLog_sound (w := (197483 / 802517)) (n := 12)
    (lo := (15702207 / 31250000)) (hi := (803953 / 1600000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302517) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 302517) = 1/(302517 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-597808903 / 500000000) (-298904451 / 250000000) (Real.log (302517 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (266850879 / 500000000) ≤ -Real.log (1000000 / 1705233) ∧
    -Real.log (1000000 / 1705233) ≤ (533701759 / 1000000000) := by
  have h := checkLog_sound (w := (705233 / 2705233)) (n := 12)
    (lo := (266850879 / 500000000)) (hi := (533701759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1705233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1705233 / 1000000) = 1/(1000000 / 1705233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (266850879 / 500000000) (533701759 / 1000000000) (Real.log (1705233 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1705233 / 1000000) = -Real.log (1000000 / 1705233) := by
    rw [show ((1705233 / 1000000) : ℝ) = ((1000000 / 1705233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (76348129 / 62500000) ≤ -Real.log (294767 / 1000000) ∧
    -Real.log (294767 / 1000000) ≤ (610785033 / 500000000) := by
  have h := checkLog_sound (w := (205233 / 794767)) (n := 12)
    (lo := (132105721 / 250000000)) (hi := (105684577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 294767) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 294767) = 1/(294767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-610785033 / 500000000) (-76348129 / 62500000) (Real.log (294767 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (210964403 / 100000000) ≤ -Real.log (31250000000 / 257665803001) ∧
    -Real.log (31250000000 / 257665803001) ≤ (1054822017 / 500000000) := by
  have h := checkLog_sound (w := (7665803001 / 507665803001)) (n := 12)
    (lo := (3020249 / 100000000)) (hi := (30202491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((257665803001 / 250000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(257665803001 / 250000000000) = 1/(31250000000 / 257665803001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (210964403 / 100000000) (1054822017 / 500000000) (Real.log (257665803001 / 31250000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (257665803001 / 31250000000) = -Real.log (31250000000 / 257665803001) := by
    rw [show ((257665803001 / 31250000000) : ℝ) = ((31250000000 / 257665803001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2118157437 / 1000000000) ≤ -Real.log (50000000000 / 415790049793) ∧
    -Real.log (50000000000 / 415790049793) ≤ (2118157441 / 1000000000) := by
  have h := checkLog_sound (w := (15790049793 / 815790049793)) (n := 12)
    (lo := (38715897 / 1000000000)) (hi := (19357949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((415790049793 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(415790049793 / 400000000000) = 1/(50000000000 / 415790049793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2118157437 / 1000000000) (2118157441 / 1000000000) (Real.log (415790049793 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (415790049793 / 50000000000) = -Real.log (50000000000 / 415790049793) := by
    rw [show ((415790049793 / 50000000000) : ℝ) = ((50000000000 / 415790049793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1724764369 / 1000000000) ≤ -Real.log (500000000000 / 2805599354747) ∧
    -Real.log (500000000000 / 2805599354747) ≤ (431191093 / 250000000) := by
  have h := checkLog_sound (w := (805599354747 / 4805599354747)) (n := 12)
    (lo := (338470009 / 1000000000)) (hi := (33847001 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2805599354747 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2805599354747 / 2000000000000) = 1/(500000000000 / 2805599354747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1724764369 / 1000000000) (431191093 / 250000000) (Real.log (2805599354747 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2805599354747 / 500000000000) = -Real.log (500000000000 / 2805599354747) := by
    rw [show ((2805599354747 / 500000000000) : ℝ) = ((500000000000 / 2805599354747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (877635911 / 500000000) ≤ -Real.log (250000000000 / 1446255008193) ∧
    -Real.log (250000000000 / 1446255008193) ≤ (70210873 / 40000000) := by
  have h := checkLog_sound (w := (446255008193 / 2446255008193)) (n := 12)
    (lo := (184488731 / 500000000)) (hi := (368977463 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1446255008193 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1446255008193 / 1000000000000) = 1/(250000000000 / 1446255008193) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (877635911 / 500000000) (70210873 / 40000000) (Real.log (1446255008193 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1446255008193 / 250000000000) = -Real.log (250000000000 / 1446255008193) := by
    rw [show ((1446255008193 / 250000000000) : ℝ) = ((250000000000 / 1446255008193) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0002

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0003Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0003
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
    -Real.log (16 / 25) ≤ (446287103 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25 / 16) = 1/(16 / 25) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (223143551 / 500000000) (446287103 / 1000000000) (Real.log (25 / 16)) := by
  have h := reflection_log_1_neg
  have he : Real.log (25 / 16) = -Real.log (16 / 25) := by
    rw [show ((25 / 16) : ℝ) = ((16 / 25) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (206669643 / 250000000) ≤ -Real.log (7 / 16) ∧
    -Real.log (7 / 16) ≤ (413339287 / 500000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(8 / 7) = 1/(7 / 16) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-413339287 / 500000000) (-206669643 / 250000000) (Real.log (7 / 16)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_3_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (23556607 / 200000000) ≤ -Real.log (8 / 9) ∧
    -Real.log (8 / 9) ≤ (29445759 / 250000000) := by
  have h := checkLog_sound (w := (1 / 17)) (n := 12)
    (lo := (23556607 / 200000000)) (hi := (29445759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9 / 8) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9 / 8) = 1/(8 / 9) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (23556607 / 200000000) (29445759 / 250000000) (Real.log (9 / 8)) := by
  have h := reflection_log_5_neg
  have he : Real.log (9 / 8) = -Real.log (8 / 9) := by
    rw [show ((9 / 8) : ℝ) = ((8 / 9) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (521607 / 3906250) ≤ -Real.log (7 / 8) ∧
    -Real.log (7 / 8) ≤ (133531393 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 15)) (n := 12)
    (lo := (521607 / 3906250)) (hi := (133531393 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8 / 7) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8 / 7) = 1/(7 / 8) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-133531393 / 1000000000) (-521607 / 3906250) (Real.log (7 / 8)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (95310179 / 1000000000) ≤ -Real.log (10 / 11) ∧
    -Real.log (10 / 11) ≤ (4765509 / 50000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 10) = 1/(10 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (95310179 / 1000000000) (4765509 / 50000000) (Real.log (11 / 10)) := by
  have h := reflection_log_7_neg
  have he : Real.log (11 / 10) = -Real.log (10 / 11) := by
    rw [show ((11 / 10) : ℝ) = ((10 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (21072103 / 200000000) ≤ -Real.log (9 / 10) ∧
    -Real.log (9 / 10) ≤ (26340129 / 250000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 9) = 1/(9 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-26340129 / 250000000) (-21072103 / 200000000) (Real.log (9 / 10)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (28896159 / 50000000) ≤ -Real.log (1000000 / 1782333) ∧
    -Real.log (1000000 / 1782333) ≤ (577923181 / 1000000000) := by
  have h := checkLog_sound (w := (782333 / 2782333)) (n := 12)
    (lo := (28896159 / 50000000)) (hi := (577923181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1782333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1782333 / 1000000) = 1/(1000000 / 1782333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (28896159 / 50000000) (577923181 / 1000000000) (Real.log (1782333 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1782333 / 1000000) = -Real.log (1000000 / 1782333) := by
    rw [show ((1782333 / 1000000) : ℝ) = ((1000000 / 1782333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (304957781 / 200000000) ≤ -Real.log (217667 / 1000000) ∧
    -Real.log (217667 / 1000000) ≤ (381197227 / 250000000) := by
  have h := checkLog_sound (w := (32333 / 467667)) (n := 12)
    (lo := (27698909 / 200000000)) (hi := (69247273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217667) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 217667) = 1/(217667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-381197227 / 250000000) (-304957781 / 200000000) (Real.log (217667 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (289337921 / 500000000) ≤ -Real.log (40000 / 71347) ∧
    -Real.log (40000 / 71347) ≤ (578675843 / 1000000000) := by
  have h := checkLog_sound (w := (31347 / 111347)) (n := 12)
    (lo := (289337921 / 500000000)) (hi := (578675843 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71347 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71347 / 40000) = 1/(40000 / 71347) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (289337921 / 500000000) (578675843 / 1000000000) (Real.log (71347 / 40000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (71347 / 40000) = -Real.log (40000 / 71347) := by
    rw [show ((71347 / 40000) : ℝ) = ((40000 / 71347) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1530973371 / 1000000000) ≤ -Real.log (8653 / 40000) ∧
    -Real.log (8653 / 40000) ≤ (765486687 / 500000000) := by
  have h := checkLog_sound (w := (1347 / 18653)) (n := 12)
    (lo := (144679011 / 1000000000)) (hi := (36169753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8653) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(10000 / 8653) = 1/(8653 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-765486687 / 500000000) (-1530973371 / 1000000000) (Real.log (8653 / 40000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (26229059 / 50000000) ≤ -Real.log (1000000 / 1689751) ∧
    -Real.log (1000000 / 1689751) ≤ (524581181 / 1000000000) := by
  have h := checkLog_sound (w := (689751 / 2689751)) (n := 12)
    (lo := (26229059 / 50000000)) (hi := (524581181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1689751 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1689751 / 1000000) = 1/(1000000 / 1689751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (26229059 / 50000000) (524581181 / 1000000000) (Real.log (1689751 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1689751 / 1000000) = -Real.log (1000000 / 1689751) := by
    rw [show ((1689751 / 1000000) : ℝ) = ((1000000 / 1689751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1170380077 / 1000000000) ≤ -Real.log (310249 / 1000000) ∧
    -Real.log (310249 / 1000000) ≤ (1170380079 / 1000000000) := by
  have h := checkLog_sound (w := (189751 / 810249)) (n := 12)
    (lo := (477232897 / 1000000000)) (hi := (238616449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 310249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 310249) = 1/(310249 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1170380079 / 1000000000) (-1170380077 / 1000000000) (Real.log (310249 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (264573577 / 500000000) ≤ -Real.log (250000 / 424371) ∧
    -Real.log (250000 / 424371) ≤ (105829431 / 200000000) := by
  have h := checkLog_sound (w := (174371 / 674371)) (n := 12)
    (lo := (264573577 / 500000000)) (hi := (105829431 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((424371 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(424371 / 250000) = 1/(250000 / 424371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (264573577 / 500000000) (105829431 / 200000000) (Real.log (424371 / 250000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (424371 / 250000) = -Real.log (250000 / 424371) := by
    rw [show ((424371 / 250000) : ℝ) = ((250000 / 424371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (1195621109 / 1000000000) ≤ -Real.log (75629 / 250000) ∧
    -Real.log (75629 / 250000) ≤ (1195621111 / 1000000000) := by
  have h := checkLog_sound (w := (49371 / 200629)) (n := 12)
    (lo := (502473929 / 1000000000)) (hi := (50247393 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 75629) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 75629) = 1/(75629 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-1195621111 / 1000000000) (-1195621109 / 1000000000) (Real.log (75629 / 250000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (420542417 / 200000000) ≤ -Real.log (500000000000 / 4094173668953) ∧
    -Real.log (500000000000 / 4094173668953) ≤ (2102712089 / 1000000000) := by
  have h := checkLog_sound (w := (94173668953 / 8094173668953)) (n := 12)
    (lo := (4654109 / 200000000)) (hi := (11635273 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4094173668953 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4094173668953 / 4000000000000) = 1/(500000000000 / 4094173668953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (420542417 / 200000000) (2102712089 / 1000000000) (Real.log (4094173668953 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4094173668953 / 500000000000) = -Real.log (500000000000 / 4094173668953) := by
    rw [show ((4094173668953 / 500000000000) : ℝ) = ((500000000000 / 4094173668953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2109649213 / 1000000000) ≤ -Real.log (100000000000 / 824534843407) ∧
    -Real.log (100000000000 / 824534843407) ≤ (2109649217 / 1000000000) := by
  have h := checkLog_sound (w := (24534843407 / 1624534843407)) (n := 12)
    (lo := (30207673 / 1000000000)) (hi := (15103837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824534843407 / 800000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(824534843407 / 800000000000) = 1/(100000000000 / 824534843407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2109649213 / 1000000000) (2109649217 / 1000000000) (Real.log (824534843407 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (824534843407 / 100000000000) = -Real.log (100000000000 / 824534843407) := by
    rw [show ((824534843407 / 100000000000) : ℝ) = ((100000000000 / 824534843407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1694961257 / 1000000000) ≤ -Real.log (500000000000 / 2723217480153) ∧
    -Real.log (500000000000 / 2723217480153) ≤ (84748063 / 50000000) := by
  have h := checkLog_sound (w := (723217480153 / 4723217480153)) (n := 12)
    (lo := (308666897 / 1000000000)) (hi := (154333449 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2723217480153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2723217480153 / 2000000000000) = 1/(500000000000 / 2723217480153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1694961257 / 1000000000) (84748063 / 50000000) (Real.log (2723217480153 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2723217480153 / 500000000000) = -Real.log (500000000000 / 2723217480153) := by
    rw [show ((2723217480153 / 500000000000) : ℝ) = ((500000000000 / 2723217480153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (215596033 / 125000000) ≤ -Real.log (500000000000 / 2805610281771) ∧
    -Real.log (500000000000 / 2805610281771) ≤ (1724768267 / 1000000000) := by
  have h := checkLog_sound (w := (805610281771 / 4805610281771)) (n := 12)
    (lo := (21154619 / 62500000)) (hi := (67694781 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2805610281771 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2805610281771 / 2000000000000) = 1/(500000000000 / 2805610281771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (215596033 / 125000000) (1724768267 / 1000000000) (Real.log (2805610281771 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2805610281771 / 500000000000) = -Real.log (500000000000 / 2805610281771) := by
    rw [show ((2805610281771 / 500000000000) : ℝ) = ((500000000000 / 2805610281771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0003

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0004Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0004
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (43825493 / 100000000) ≤ -Real.log (20 / 31) ∧
    -Real.log (20 / 31) ≤ (438254931 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 51)) (n := 12)
    (lo := (43825493 / 100000000)) (hi := (438254931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31 / 20) = 1/(20 / 31) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (43825493 / 100000000) (438254931 / 1000000000) (Real.log (31 / 20)) := by
  have h := reflection_log_1_neg
  have he : Real.log (31 / 20) = -Real.log (20 / 31) := by
    rw [show ((31 / 20) : ℝ) = ((20 / 31) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (159701539 / 200000000) ≤ -Real.log (9 / 20) ∧
    -Real.log (9 / 20) ≤ (798507697 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10 / 9) = 1/(9 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-798507697 / 1000000000) (-159701539 / 200000000) (Real.log (9 / 20)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (10753943 / 25000000) ≤ -Real.log (80 / 123) ∧
    -Real.log (80 / 123) ≤ (430157721 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 203)) (n := 12)
    (lo := (10753943 / 25000000)) (hi := (430157721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 80) = 1/(80 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (10753943 / 25000000) (430157721 / 1000000000) (Real.log (123 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (123 / 80) = -Real.log (80 / 123) := by
    rw [show ((123 / 80) : ℝ) = ((80 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (771108721 / 1000000000) ≤ -Real.log (37 / 80) ∧
    -Real.log (37 / 80) ≤ (771108723 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 37) = 1/(37 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-771108723 / 1000000000) (-771108721 / 1000000000) (Real.log (37 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (95310179 / 1000000000) ≤ -Real.log (10 / 11) ∧
    -Real.log (10 / 11) ≤ (4765509 / 50000000) := by
  have h := checkLog_sound (w := (1 / 21)) (n := 12)
    (lo := (95310179 / 1000000000)) (hi := (4765509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11 / 10) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11 / 10) = 1/(10 / 11) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (95310179 / 1000000000) (4765509 / 50000000) (Real.log (11 / 10)) := by
  have h := reflection_log_5_neg
  have he : Real.log (11 / 10) = -Real.log (10 / 11) := by
    rw [show ((11 / 10) : ℝ) = ((10 / 11) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (21072103 / 200000000) ≤ -Real.log (9 / 10) ∧
    -Real.log (9 / 10) ≤ (26340129 / 250000000) := by
  have h := checkLog_sound (w := (1 / 19)) (n := 12)
    (lo := (21072103 / 200000000)) (hi := (26340129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10 / 9) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10 / 9) = 1/(9 / 10) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-26340129 / 250000000) (-21072103 / 200000000) (Real.log (9 / 10)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (72320661 / 1000000000) ≤ -Real.log (40 / 43) ∧
    -Real.log (40 / 43) ≤ (36160331 / 500000000) := by
  have h := checkLog_sound (w := (3 / 83)) (n := 12)
    (lo := (72320661 / 1000000000)) (hi := (36160331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 40) = 1/(40 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (72320661 / 1000000000) (36160331 / 500000000) (Real.log (43 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (43 / 40) = -Real.log (40 / 43) := by
    rw [show ((43 / 40) : ℝ) = ((40 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77961541 / 1000000000) ≤ -Real.log (37 / 40) ∧
    -Real.log (37 / 40) ≤ (38980771 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 37) = 1/(37 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38980771 / 500000000) (-77961541 / 1000000000) (Real.log (37 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (288668349 / 500000000) ≤ -Real.log (125000 / 222661) ∧
    -Real.log (125000 / 222661) ≤ (577336699 / 1000000000) := by
  have h := checkLog_sound (w := (97661 / 347661)) (n := 12)
    (lo := (288668349 / 500000000)) (hi := (577336699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((222661 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(222661 / 125000) = 1/(125000 / 222661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (288668349 / 500000000) (577336699 / 1000000000) (Real.log (222661 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (222661 / 125000) = -Real.log (125000 / 222661) := by
    rw [show ((222661 / 125000) : ℝ) = ((125000 / 222661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (759999741 / 500000000) ≤ -Real.log (27339 / 125000) ∧
    -Real.log (27339 / 125000) ≤ (303999897 / 200000000) := by
  have h := checkLog_sound (w := (3911 / 58589)) (n := 12)
    (lo := (66852561 / 500000000)) (hi := (133705123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27339) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(31250 / 27339) = 1/(27339 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-303999897 / 200000000) (-759999741 / 500000000) (Real.log (27339 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (577923741 / 1000000000) ≤ -Real.log (500000 / 891167) ∧
    -Real.log (500000 / 891167) ≤ (288961871 / 500000000) := by
  have h := checkLog_sound (w := (391167 / 1391167)) (n := 12)
    (lo := (577923741 / 1000000000)) (hi := (288961871 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((891167 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(891167 / 500000) = 1/(500000 / 891167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (577923741 / 1000000000) (288961871 / 500000000) (Real.log (891167 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (891167 / 500000) = -Real.log (500000 / 891167) := by
    rw [show ((891167 / 500000) : ℝ) = ((500000 / 891167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (3049587 / 2000000) ≤ -Real.log (108833 / 500000) ∧
    -Real.log (108833 / 500000) ≤ (1524793503 / 1000000000) := by
  have h := checkLog_sound (w := (16167 / 233833)) (n := 12)
    (lo := (6924957 / 50000000)) (hi := (138499141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 108833) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 108833) = 1/(108833 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1524793503 / 1000000000) (-3049587 / 2000000) (Real.log (108833 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (260001293 / 500000000) ≤ -Real.log (62500 / 105127) ∧
    -Real.log (62500 / 105127) ≤ (520002587 / 1000000000) := by
  have h := checkLog_sound (w := (42627 / 167627)) (n := 12)
    (lo := (260001293 / 500000000)) (hi := (520002587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105127 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105127 / 62500) = 1/(62500 / 105127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (260001293 / 500000000) (520002587 / 1000000000) (Real.log (105127 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (105127 / 62500) = -Real.log (62500 / 105127) := by
    rw [show ((105127 / 62500) : ℝ) = ((62500 / 105127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (1145804529 / 1000000000) ≤ -Real.log (19873 / 62500) ∧
    -Real.log (19873 / 62500) ≤ (1145804531 / 1000000000) := by
  have h := checkLog_sound (w := (11377 / 51123)) (n := 12)
    (lo := (452657349 / 1000000000)) (hi := (9053147 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19873) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 19873) = 1/(19873 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1145804531 / 1000000000) (-1145804529 / 1000000000) (Real.log (19873 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (131145443 / 250000000) ≤ -Real.log (125000 / 211219) ∧
    -Real.log (125000 / 211219) ≤ (524581773 / 1000000000) := by
  have h := checkLog_sound (w := (86219 / 336219)) (n := 12)
    (lo := (131145443 / 250000000)) (hi := (524581773 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((211219 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(211219 / 125000) = 1/(125000 / 211219) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (131145443 / 250000000) (524581773 / 1000000000) (Real.log (211219 / 125000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (211219 / 125000) = -Real.log (125000 / 211219) := by
    rw [show ((211219 / 125000) : ℝ) = ((125000 / 211219) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (11703833 / 10000000) ≤ -Real.log (38781 / 125000) ∧
    -Real.log (38781 / 125000) ≤ (585191651 / 500000000) := by
  have h := checkLog_sound (w := (23719 / 101281)) (n := 12)
    (lo := (11930903 / 25000000)) (hi := (477236121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 38781) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 38781) = 1/(38781 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-585191651 / 500000000) (-11703833 / 10000000) (Real.log (38781 / 125000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2097336179 / 1000000000) ≤ -Real.log (500000000000 / 4072222831851) ∧
    -Real.log (500000000000 / 4072222831851) ≤ (2097336183 / 1000000000) := by
  have h := checkLog_sound (w := (72222831851 / 8072222831851)) (n := 12)
    (lo := (17894639 / 1000000000)) (hi := (223683 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4072222831851 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4072222831851 / 4000000000000) = 1/(500000000000 / 4072222831851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2097336179 / 1000000000) (2097336183 / 1000000000) (Real.log (4072222831851 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4072222831851 / 500000000000) = -Real.log (500000000000 / 4072222831851) := by
    rw [show ((4072222831851 / 500000000000) : ℝ) = ((500000000000 / 4072222831851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (52567931 / 25000000) ≤ -Real.log (250000000000 / 2047097387741) ∧
    -Real.log (250000000000 / 2047097387741) ≤ (525679311 / 250000000) := by
  have h := checkLog_sound (w := (47097387741 / 4047097387741)) (n := 12)
    (lo := (232757 / 10000000)) (hi := (23275701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2047097387741 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2047097387741 / 2000000000000) = 1/(250000000000 / 2047097387741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (52567931 / 25000000) (525679311 / 250000000) (Real.log (2047097387741 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2047097387741 / 250000000000) = -Real.log (250000000000 / 2047097387741) := by
    rw [show ((2047097387741 / 250000000000) : ℝ) = ((250000000000 / 2047097387741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (333161423 / 200000000) ≤ -Real.log (20000000000 / 105798822523) ∧
    -Real.log (20000000000 / 105798822523) ≤ (832903559 / 500000000) := by
  have h := checkLog_sound (w := (25798822523 / 185798822523)) (n := 12)
    (lo := (55902551 / 200000000)) (hi := (69878189 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105798822523 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(105798822523 / 80000000000) = 1/(20000000000 / 105798822523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (333161423 / 200000000) (832903559 / 500000000) (Real.log (105798822523 / 20000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (105798822523 / 20000000000) = -Real.log (20000000000 / 105798822523) := by
    rw [show ((105798822523 / 20000000000) : ℝ) = ((20000000000 / 105798822523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (105935317 / 62500000) ≤ -Real.log (250000000000 / 1361613934659) ∧
    -Real.log (250000000000 / 1361613934659) ≤ (67798603 / 40000000) := by
  have h := checkLog_sound (w := (361613934659 / 2361613934659)) (n := 12)
    (lo := (38583839 / 125000000)) (hi := (308670713 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361613934659 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1361613934659 / 1000000000000) = 1/(250000000000 / 1361613934659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (105935317 / 62500000) (67798603 / 40000000) (Real.log (1361613934659 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1361613934659 / 250000000000) = -Real.log (250000000000 / 1361613934659) := by
    rw [show ((1361613934659 / 250000000000) : ℝ) = ((250000000000 / 1361613934659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0004

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0005Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0005
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (10753943 / 25000000) ≤ -Real.log (80 / 123) ∧
    -Real.log (80 / 123) ≤ (430157721 / 1000000000) := by
  have h := checkLog_sound (w := (43 / 203)) (n := 12)
    (lo := (10753943 / 25000000)) (hi := (430157721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123 / 80) = 1/(80 / 123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (10753943 / 25000000) (430157721 / 1000000000) (Real.log (123 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (123 / 80) = -Real.log (80 / 123) := by
    rw [show ((123 / 80) : ℝ) = ((80 / 123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (771108721 / 1000000000) ≤ -Real.log (37 / 80) ∧
    -Real.log (37 / 80) ≤ (771108723 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(40 / 37) = 1/(37 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-771108723 / 1000000000) (-771108721 / 1000000000) (Real.log (37 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (42199441 / 100000000) ≤ -Real.log (40 / 61) ∧
    -Real.log (40 / 61) ≤ (421994411 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 101)) (n := 12)
    (lo := (42199441 / 100000000)) (hi := (421994411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 40) = 1/(40 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (42199441 / 100000000) (421994411 / 1000000000) (Real.log (61 / 40)) := by
  have h := reflection_log_3_neg
  have he : Real.log (61 / 40) = -Real.log (40 / 61) := by
    rw [show ((61 / 40) : ℝ) = ((40 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (372220237 / 500000000) ≤ -Real.log (19 / 40) ∧
    -Real.log (19 / 40) ≤ (186110119 / 250000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 19) = 1/(19 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-186110119 / 250000000) (-372220237 / 500000000) (Real.log (19 / 40)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (72320661 / 1000000000) ≤ -Real.log (40 / 43) ∧
    -Real.log (40 / 43) ≤ (36160331 / 500000000) := by
  have h := checkLog_sound (w := (3 / 83)) (n := 12)
    (lo := (72320661 / 1000000000)) (hi := (36160331 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 40) = 1/(40 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (72320661 / 1000000000) (36160331 / 500000000) (Real.log (43 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (43 / 40) = -Real.log (40 / 43) := by
    rw [show ((43 / 40) : ℝ) = ((40 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (77961541 / 1000000000) ≤ -Real.log (37 / 40) ∧
    -Real.log (37 / 40) ≤ (38980771 / 500000000) := by
  have h := checkLog_sound (w := (3 / 77)) (n := 12)
    (lo := (77961541 / 1000000000)) (hi := (38980771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 37) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40 / 37) = 1/(37 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-38980771 / 500000000) (-77961541 / 1000000000) (Real.log (37 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (12197541 / 250000000) ≤ -Real.log (20 / 21) ∧
    -Real.log (20 / 21) ≤ (9758033 / 200000000) := by
  have h := checkLog_sound (w := (1 / 41)) (n := 12)
    (lo := (12197541 / 250000000)) (hi := (9758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 20) = 1/(20 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (12197541 / 250000000) (9758033 / 200000000) (Real.log (21 / 20)) := by
  have h := reflection_log_7_neg
  have he : Real.log (21 / 20) = -Real.log (20 / 21) := by
    rw [show ((21 / 20) : ℝ) = ((20 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (25646647 / 500000000) ≤ -Real.log (19 / 20) ∧
    -Real.log (19 / 20) ≤ (10258659 / 200000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 19) = 1/(19 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-10258659 / 200000000) (-25646647 / 500000000) (Real.log (19 / 20)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (144229453 / 250000000) ≤ -Real.log (500000 / 890271) ∧
    -Real.log (500000 / 890271) ≤ (576917813 / 1000000000) := by
  have h := checkLog_sound (w := (390271 / 1390271)) (n := 12)
    (lo := (144229453 / 250000000)) (hi := (576917813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((890271 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(890271 / 500000) = 1/(500000 / 890271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (144229453 / 250000000) (576917813 / 1000000000) (Real.log (890271 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (890271 / 500000) = -Real.log (500000 / 890271) := by
    rw [show ((890271 / 500000) : ℝ) = ((500000 / 890271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1516594407 / 1000000000) ≤ -Real.log (109729 / 500000) ∧
    -Real.log (109729 / 500000) ≤ (151659441 / 100000000) := by
  have h := checkLog_sound (w := (15271 / 234729)) (n := 12)
    (lo := (130300047 / 1000000000)) (hi := (8143753 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109729) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(125000 / 109729) = 1/(109729 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-151659441 / 100000000) (-1516594407 / 1000000000) (Real.log (109729 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (577337259 / 1000000000) ≤ -Real.log (1000000 / 1781289) ∧
    -Real.log (1000000 / 1781289) ≤ (28866863 / 50000000) := by
  have h := checkLog_sound (w := (781289 / 2781289)) (n := 12)
    (lo := (577337259 / 1000000000)) (hi := (28866863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1781289 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1781289 / 1000000) = 1/(1000000 / 1781289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (577337259 / 1000000000) (28866863 / 50000000) (Real.log (1781289 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1781289 / 1000000) = -Real.log (1000000 / 1781289) := by
    rw [show ((1781289 / 1000000) : ℝ) = ((1000000 / 1781289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (760002027 / 500000000) ≤ -Real.log (218711 / 1000000) ∧
    -Real.log (218711 / 1000000) ≤ (1520004057 / 1000000000) := by
  have h := checkLog_sound (w := (31289 / 468711)) (n := 12)
    (lo := (66854847 / 500000000)) (hi := (26741939 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 218711) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 218711) = 1/(218711 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1520004057 / 1000000000) (-760002027 / 500000000) (Real.log (218711 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (515409501 / 1000000000) ≤ -Real.log (250000 / 418581) ∧
    -Real.log (250000 / 418581) ≤ (257704751 / 500000000) := by
  have h := checkLog_sound (w := (168581 / 668581)) (n := 12)
    (lo := (515409501 / 1000000000)) (hi := (257704751 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((418581 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(418581 / 250000) = 1/(250000 / 418581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (515409501 / 1000000000) (257704751 / 500000000) (Real.log (418581 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (418581 / 250000) = -Real.log (250000 / 418581) := by
    rw [show ((418581 / 250000) : ℝ) = ((250000 / 418581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (35057883 / 31250000) ≤ -Real.log (81419 / 250000) ∧
    -Real.log (81419 / 250000) ≤ (560926129 / 500000000) := by
  have h := checkLog_sound (w := (43581 / 206419)) (n := 12)
    (lo := (107176269 / 250000000)) (hi := (428705077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 81419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 81419) = 1/(81419 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-560926129 / 500000000) (-35057883 / 31250000) (Real.log (81419 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (26000159 / 50000000) ≤ -Real.log (1000000 / 1682033) ∧
    -Real.log (1000000 / 1682033) ≤ (520003181 / 1000000000) := by
  have h := checkLog_sound (w := (682033 / 2682033)) (n := 12)
    (lo := (26000159 / 50000000)) (hi := (520003181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1682033 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1682033 / 1000000) = 1/(1000000 / 1682033) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (26000159 / 50000000) (520003181 / 1000000000) (Real.log (1682033 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1682033 / 1000000) = -Real.log (1000000 / 1682033) := by
    rw [show ((1682033 / 1000000) : ℝ) = ((1000000 / 1682033) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (572903837 / 500000000) ≤ -Real.log (317967 / 1000000) ∧
    -Real.log (317967 / 1000000) ≤ (286451919 / 250000000) := by
  have h := checkLog_sound (w := (182033 / 817967)) (n := 12)
    (lo := (226330247 / 500000000)) (hi := (90532099 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 317967) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 317967) = 1/(317967 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-286451919 / 250000000) (-572903837 / 500000000) (Real.log (317967 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (2093512219 / 1000000000) ≤ -Real.log (500000000000 / 4056680549353) ∧
    -Real.log (500000000000 / 4056680549353) ≤ (2093512223 / 1000000000) := by
  have h := checkLog_sound (w := (56680549353 / 8056680549353)) (n := 12)
    (lo := (14070679 / 1000000000)) (hi := (351767 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4056680549353 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4056680549353 / 4000000000000) = 1/(500000000000 / 4056680549353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (2093512219 / 1000000000) (2093512223 / 1000000000) (Real.log (4056680549353 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4056680549353 / 500000000000) = -Real.log (500000000000 / 4056680549353) := by
    rw [show ((4056680549353 / 500000000000) : ℝ) = ((500000000000 / 4056680549353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2097341313 / 1000000000) ≤ -Real.log (50000000000 / 407224373717) ∧
    -Real.log (50000000000 / 407224373717) ≤ (2097341317 / 1000000000) := by
  have h := checkLog_sound (w := (7224373717 / 807224373717)) (n := 12)
    (lo := (17899773 / 1000000000)) (hi := (8949887 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((407224373717 / 400000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(407224373717 / 400000000000) = 1/(50000000000 / 407224373717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2097341313 / 1000000000) (2097341317 / 1000000000) (Real.log (407224373717 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (407224373717 / 50000000000) = -Real.log (50000000000 / 407224373717) := by
    rw [show ((407224373717 / 50000000000) : ℝ) = ((50000000000 / 407224373717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1637261757 / 1000000000) ≤ -Real.log (500000000000 / 2570536361291) ∧
    -Real.log (500000000000 / 2570536361291) ≤ (5116443 / 3125000) := by
  have h := checkLog_sound (w := (570536361291 / 4570536361291)) (n := 12)
    (lo := (250967397 / 1000000000)) (hi := (125483699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2570536361291 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2570536361291 / 2000000000000) = 1/(500000000000 / 2570536361291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1637261757 / 1000000000) (5116443 / 3125000) (Real.log (2570536361291 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2570536361291 / 500000000000) = -Real.log (500000000000 / 2570536361291) := by
    rw [show ((2570536361291 / 500000000000) : ℝ) = ((500000000000 / 2570536361291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (832905427 / 500000000) ≤ -Real.log (500000000000 / 2644980453947) ∧
    -Real.log (500000000000 / 2644980453947) ≤ (1665810857 / 1000000000) := by
  have h := checkLog_sound (w := (644980453947 / 4644980453947)) (n := 12)
    (lo := (139758247 / 500000000)) (hi := (55903299 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2644980453947 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2644980453947 / 2000000000000) = 1/(500000000000 / 2644980453947) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (832905427 / 500000000) (1665810857 / 1000000000) (Real.log (2644980453947 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (2644980453947 / 500000000000) = -Real.log (500000000000 / 2644980453947) := by
    rw [show ((2644980453947 / 500000000000) : ℝ) = ((500000000000 / 2644980453947) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0005

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0006Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0006
open GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed

theorem reflection_log_0_neg : (34657359 / 50000000) ≤ -Real.log (1 / 2) ∧
    -Real.log (1 / 2) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2 / 1) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2 / 1) = 1/(1 / 2) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_0 : Bounds (34657359 / 50000000) (693147181 / 1000000000) (Real.log (2 / 1)) := by
  have h := reflection_log_0_neg
  have he : Real.log (2 / 1) = -Real.log (1 / 2) := by
    rw [show ((2 / 1) : ℝ) = ((1 / 2) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1_neg : (42199441 / 100000000) ≤ -Real.log (40 / 61) ∧
    -Real.log (40 / 61) ≤ (421994411 / 1000000000) := by
  have h := checkLog_sound (w := (21 / 101)) (n := 12)
    (lo := (42199441 / 100000000)) (hi := (421994411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((61 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(61 / 40) = 1/(40 / 61) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (42199441 / 100000000) (421994411 / 1000000000) (Real.log (61 / 40)) := by
  have h := reflection_log_1_neg
  have he : Real.log (61 / 40) = -Real.log (40 / 61) := by
    rw [show ((61 / 40) : ℝ) = ((40 / 61) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (372220237 / 500000000) ≤ -Real.log (19 / 40) ∧
    -Real.log (19 / 40) ≤ (186110119 / 250000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20 / 19) = 1/(19 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-186110119 / 250000000) (-372220237 / 500000000) (Real.log (19 / 40)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (104471907 / 250000000) ≤ -Real.log (160 / 243) ∧
    -Real.log (160 / 243) ≤ (417887629 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 403)) (n := 12)
    (lo := (104471907 / 250000000)) (hi := (417887629 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((243 / 160) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(243 / 160) = 1/(160 / 243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (104471907 / 250000000) (417887629 / 1000000000) (Real.log (243 / 160)) := by
  have h := reflection_log_3_neg
  have he : Real.log (243 / 160) = -Real.log (160 / 243) := by
    rw [show ((243 / 160) : ℝ) = ((160 / 243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (91421049 / 125000000) ≤ -Real.log (77 / 160) ∧
    -Real.log (77 / 160) ≤ (365684197 / 500000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(80 / 77) = 1/(77 / 160) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-365684197 / 500000000) (-91421049 / 125000000) (Real.log (77 / 160)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (12197541 / 250000000) ≤ -Real.log (20 / 21) ∧
    -Real.log (20 / 21) ≤ (9758033 / 200000000) := by
  have h := checkLog_sound (w := (1 / 41)) (n := 12)
    (lo := (12197541 / 250000000)) (hi := (9758033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21 / 20) = 1/(20 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (12197541 / 250000000) (9758033 / 200000000) (Real.log (21 / 20)) := by
  have h := reflection_log_5_neg
  have he : Real.log (21 / 20) = -Real.log (20 / 21) := by
    rw [show ((21 / 20) : ℝ) = ((20 / 21) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (25646647 / 500000000) ≤ -Real.log (19 / 20) ∧
    -Real.log (19 / 20) ≤ (10258659 / 200000000) := by
  have h := checkLog_sound (w := (1 / 39)) (n := 12)
    (lo := (25646647 / 500000000)) (hi := (10258659 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 19) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 19) = 1/(19 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-10258659 / 200000000) (-25646647 / 500000000) (Real.log (19 / 20)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (36813973 / 1000000000) ≤ -Real.log (80 / 83) ∧
    -Real.log (80 / 83) ≤ (18406987 / 500000000) := by
  have h := checkLog_sound (w := (3 / 163)) (n := 12)
    (lo := (36813973 / 1000000000)) (hi := (18406987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((83 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(83 / 80) = 1/(80 / 83) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (36813973 / 1000000000) (18406987 / 500000000) (Real.log (83 / 80)) := by
  have h := reflection_log_7_neg
  have he : Real.log (83 / 80) = -Real.log (80 / 83) := by
    rw [show ((83 / 80) : ℝ) = ((80 / 83) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (9555303 / 250000000) ≤ -Real.log (77 / 80) ∧
    -Real.log (77 / 80) ≤ (38221213 / 1000000000) := by
  have h := checkLog_sound (w := (3 / 157)) (n := 12)
    (lo := (9555303 / 250000000)) (hi := (38221213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 77) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 77) = 1/(77 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-38221213 / 1000000000) (-9555303 / 250000000) (Real.log (77 / 80)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (115354131 / 200000000) ≤ -Real.log (25000 / 44507) ∧
    -Real.log (25000 / 44507) ≤ (18024083 / 31250000) := by
  have h := checkLog_sound (w := (19507 / 69507)) (n := 12)
    (lo := (115354131 / 200000000)) (hi := (18024083 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44507 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(44507 / 25000) = 1/(25000 / 44507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (115354131 / 200000000) (18024083 / 31250000) (Real.log (44507 / 25000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (44507 / 25000) = -Real.log (25000 / 44507) := by
    rw [show ((44507 / 25000) : ℝ) = ((25000 / 44507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1515401269 / 1000000000) ≤ -Real.log (5493 / 25000) ∧
    -Real.log (5493 / 25000) ≤ (189425159 / 125000000) := by
  have h := checkLog_sound (w := (757 / 11743)) (n := 12)
    (lo := (129106909 / 1000000000)) (hi := (12910691 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 5493) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(6250 / 5493) = 1/(5493 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-189425159 / 125000000) (-1515401269 / 1000000000) (Real.log (5493 / 25000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (576918373 / 1000000000) ≤ -Real.log (1000000 / 1780543) ∧
    -Real.log (1000000 / 1780543) ≤ (288459187 / 500000000) := by
  have h := checkLog_sound (w := (780543 / 2780543)) (n := 12)
    (lo := (576918373 / 1000000000)) (hi := (288459187 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1780543 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1780543 / 1000000) = 1/(1000000 / 1780543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (576918373 / 1000000000) (288459187 / 500000000) (Real.log (1780543 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1780543 / 1000000) = -Real.log (1000000 / 1780543) := by
    rw [show ((1780543 / 1000000) : ℝ) = ((1000000 / 1780543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (379149741 / 250000000) ≤ -Real.log (219457 / 1000000) ∧
    -Real.log (219457 / 1000000) ≤ (1516598967 / 1000000000) := by
  have h := checkLog_sound (w := (30543 / 469457)) (n := 12)
    (lo := (32576151 / 250000000)) (hi := (26060921 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 219457) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(250000 / 219457) = 1/(219457 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1516598967 / 1000000000) (-379149741 / 250000000) (Real.log (219457 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (513106819 / 1000000000) ≤ -Real.log (1000000 / 1670473) ∧
    -Real.log (1000000 / 1670473) ≤ (25655341 / 50000000) := by
  have h := checkLog_sound (w := (670473 / 2670473)) (n := 12)
    (lo := (513106819 / 1000000000)) (hi := (25655341 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1670473 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1670473 / 1000000) = 1/(1000000 / 1670473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (513106819 / 1000000000) (25655341 / 50000000) (Real.log (1670473 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1670473 / 1000000) = -Real.log (1000000 / 1670473) := by
    rw [show ((1670473 / 1000000) : ℝ) = ((1000000 / 1670473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (222019397 / 200000000) ≤ -Real.log (329527 / 1000000) ∧
    -Real.log (329527 / 1000000) ≤ (1110096987 / 1000000000) := by
  have h := checkLog_sound (w := (170473 / 829527)) (n := 12)
    (lo := (83389961 / 200000000)) (hi := (208474903 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 329527) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 329527) = 1/(329527 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-1110096987 / 1000000000) (-222019397 / 200000000) (Real.log (329527 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (257705049 / 500000000) ≤ -Real.log (40000 / 66973) ∧
    -Real.log (40000 / 66973) ≤ (515410099 / 1000000000) := by
  have h := checkLog_sound (w := (26973 / 106973)) (n := 12)
    (lo := (257705049 / 500000000)) (hi := (515410099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66973 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(66973 / 40000) = 1/(40000 / 66973) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (257705049 / 500000000) (515410099 / 1000000000) (Real.log (66973 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (66973 / 40000) = -Real.log (40000 / 66973) := by
    rw [show ((66973 / 40000) : ℝ) = ((40000 / 66973) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (560927663 / 500000000) ≤ -Real.log (13027 / 40000) ∧
    -Real.log (13027 / 40000) ≤ (35057979 / 31250000) := by
  have h := checkLog_sound (w := (6973 / 33027)) (n := 12)
    (lo := (214354073 / 500000000)) (hi := (428708147 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 13027) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 13027) = 1/(13027 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-35057979 / 31250000) (-560927663 / 500000000) (Real.log (13027 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (523042981 / 250000000) ≤ -Real.log (500000000000 / 4051247041689) ∧
    -Real.log (500000000000 / 4051247041689) ≤ (261521491 / 125000000) := by
  have h := checkLog_sound (w := (51247041689 / 8051247041689)) (n := 12)
    (lo := (795649 / 62500000)) (hi := (2546077 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4051247041689 / 4000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(4051247041689 / 4000000000000) = 1/(500000000000 / 4051247041689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (523042981 / 250000000) (261521491 / 125000000) (Real.log (4051247041689 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (4051247041689 / 500000000000) = -Real.log (500000000000 / 4051247041689) := by
    rw [show ((4051247041689 / 500000000000) : ℝ) = ((500000000000 / 4051247041689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (2093517337 / 1000000000) ≤ -Real.log (250000000000 / 2028350656393) ∧
    -Real.log (250000000000 / 2028350656393) ≤ (2093517341 / 1000000000) := by
  have h := checkLog_sound (w := (28350656393 / 4028350656393)) (n := 12)
    (lo := (14075797 / 1000000000)) (hi := (7037899 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2028350656393 / 2000000000000) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(2028350656393 / 2000000000000) = 1/(250000000000 / 2028350656393) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (2093517337 / 1000000000) (2093517341 / 1000000000) (Real.log (2028350656393 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2028350656393 / 250000000000) = -Real.log (250000000000 / 2028350656393) := by
    rw [show ((2028350656393 / 250000000000) : ℝ) = ((250000000000 / 2028350656393) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (405800951 / 250000000) ≤ -Real.log (500000000000 / 2534652699171) ∧
    -Real.log (500000000000 / 2534652699171) ≤ (1623203807 / 1000000000) := by
  have h := checkLog_sound (w := (534652699171 / 4534652699171)) (n := 12)
    (lo := (59227361 / 250000000)) (hi := (47381889 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2534652699171 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2534652699171 / 2000000000000) = 1/(500000000000 / 2534652699171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (405800951 / 250000000) (1623203807 / 1000000000) (Real.log (2534652699171 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (2534652699171 / 500000000000) = -Real.log (500000000000 / 2534652699171) := by
    rw [show ((2534652699171 / 500000000000) : ℝ) = ((500000000000 / 2534652699171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (65490617 / 40000000) ≤ -Real.log (100000000000 / 514109157903) ∧
    -Real.log (100000000000 / 514109157903) ≤ (409316357 / 250000000) := by
  have h := checkLog_sound (w := (114109157903 / 914109157903)) (n := 12)
    (lo := (50194213 / 200000000)) (hi := (125485533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((514109157903 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(514109157903 / 400000000000) = 1/(100000000000 / 514109157903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (65490617 / 40000000) (409316357 / 250000000) (Real.log (514109157903 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (514109157903 / 100000000000) = -Real.log (100000000000 / 514109157903) := by
    rw [show ((514109157903 / 100000000000) : ℝ) = ((100000000000 / 514109157903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0006

end


