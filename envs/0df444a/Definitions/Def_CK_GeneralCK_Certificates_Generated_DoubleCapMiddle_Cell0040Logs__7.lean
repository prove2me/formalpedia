-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0040Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapMiddle_Cell0040Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T06:00:48.813121+00:00
-- url     : https://prove2.me/theorems/9218ac12-a301-4387-9815-9ef9090e73c4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0040Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0041Logs, GeneralCK.Certificat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0040Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0044Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0045Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0046Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0040Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0044Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0045Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0046Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0040Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0041Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0042Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0043Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0044Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0045Logs, GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0046Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0040Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0041Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0042Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0043Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0044Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0045Logs, GeneralCK/Certificates/Generated/DoubleCapMiddle/Cell0046Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0040Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0040
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

theorem reflection_log_1_neg : (382548261 / 1000000000) ≤ -Real.log (2560 / 3753) ∧
    -Real.log (2560 / 3753) ≤ (191274131 / 500000000) := by
  have h := checkLog_sound (w := (1193 / 6313)) (n := 12)
    (lo := (382548261 / 1000000000)) (hi := (191274131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3753 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3753 / 2560) = 1/(2560 / 3753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (382548261 / 1000000000) (191274131 / 500000000) (Real.log (3753 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3753 / 2560) = -Real.log (2560 / 3753) := by
    rw [show ((3753 / 2560) : ℝ) = ((2560 / 3753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (6273887 / 10000000) ≤ -Real.log (1367 / 2560) ∧
    -Real.log (1367 / 2560) ≤ (627388701 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3927)) (n := 12)
    (lo := (6273887 / 10000000)) (hi := (627388701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1367) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1367) = 1/(1367 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-627388701 / 1000000000) (-6273887 / 10000000) (Real.log (1367 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (381748581 / 1000000000) ≤ -Real.log (256 / 375) ∧
    -Real.log (256 / 375) ≤ (190874291 / 500000000) := by
  have h := checkLog_sound (w := (119 / 631)) (n := 12)
    (lo := (381748581 / 1000000000)) (hi := (190874291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375 / 256) = 1/(256 / 375) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (381748581 / 1000000000) (190874291 / 500000000) (Real.log (375 / 256)) := by
  have h := reflection_log_3_neg
  have he : Real.log (375 / 256) = -Real.log (256 / 375) := by
    rw [show ((375 / 256) : ℝ) = ((256 / 375) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (312598259 / 500000000) ≤ -Real.log (137 / 256) ∧
    -Real.log (137 / 256) ≤ (625196519 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 393)) (n := 12)
    (lo := (312598259 / 500000000)) (hi := (625196519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 137) = 1/(137 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-625196519 / 1000000000) (-312598259 / 500000000) (Real.log (137 / 256)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (65857191 / 100000000) ≤ -Real.log (1280 / 2473) ∧
    -Real.log (1280 / 2473) ≤ (658571911 / 1000000000) := by
  have h := checkLog_sound (w := (1193 / 3753)) (n := 12)
    (lo := (65857191 / 100000000)) (hi := (658571911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2473 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2473 / 1280) = 1/(1280 / 2473) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (65857191 / 100000000) (658571911 / 1000000000) (Real.log (2473 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2473 / 1280) = -Real.log (1280 / 2473) := by
    rw [show ((2473 / 1280) : ℝ) = ((1280 / 2473) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (672176809 / 250000000) ≤ -Real.log (87 / 1280) ∧
    -Real.log (87 / 1280) ≤ (67217681 / 25000000) := by
  have h := checkLog_sound (w := (73 / 247)) (n := 12)
    (lo := (19039553 / 31250000)) (hi := (609265697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 87) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 87) = 1/(87 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-67217681 / 25000000) (-672176809 / 250000000) (Real.log (87 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (82169759 / 125000000) ≤ -Real.log (128 / 247) ∧
    -Real.log (128 / 247) ≤ (657358073 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 375)) (n := 12)
    (lo := (82169759 / 125000000)) (hi := (657358073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 128) = 1/(128 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (82169759 / 125000000) (657358073 / 1000000000) (Real.log (247 / 128)) := by
  have h := reflection_log_7_neg
  have he : Real.log (247 / 128) = -Real.log (128 / 247) := by
    rw [show ((247 / 128) : ℝ) = ((128 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (663701421 / 250000000) ≤ -Real.log (9 / 128) ∧
    -Real.log (9 / 128) ≤ (331850711 / 125000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 9) = 1/(9 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-331850711 / 125000000) (-663701421 / 250000000) (Real.log (9 / 128)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (66330149 / 125000000) ≤ -Real.log (500000 / 850011) ∧
    -Real.log (500000 / 850011) ≤ (530641193 / 1000000000) := by
  have h := checkLog_sound (w := (350011 / 1350011)) (n := 12)
    (lo := (66330149 / 125000000)) (hi := (530641193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((850011 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(850011 / 500000) = 1/(500000 / 850011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (66330149 / 125000000) (530641193 / 1000000000) (Real.log (850011 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (850011 / 500000) = -Real.log (500000 / 850011) := by
    rw [show ((850011 / 500000) : ℝ) = ((500000 / 850011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1204046139 / 1000000000) ≤ -Real.log (149989 / 500000) ∧
    -Real.log (149989 / 500000) ≤ (1204046141 / 1000000000) := by
  have h := checkLog_sound (w := (100011 / 399989)) (n := 12)
    (lo := (510898959 / 1000000000)) (hi := (6386237 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 149989) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 149989) = 1/(149989 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1204046141 / 1000000000) (-1204046139 / 1000000000) (Real.log (149989 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (33247519 / 62500000) ≤ -Real.log (500000 / 851133) ∧
    -Real.log (500000 / 851133) ≤ (106392061 / 200000000) := by
  have h := checkLog_sound (w := (351133 / 1351133)) (n := 12)
    (lo := (33247519 / 62500000)) (hi := (106392061 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((851133 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(851133 / 500000) = 1/(500000 / 851133) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (33247519 / 62500000) (106392061 / 200000000) (Real.log (851133 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (851133 / 500000) = -Real.log (500000 / 851133) := by
    rw [show ((851133 / 500000) : ℝ) = ((500000 / 851133) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1211554807 / 1000000000) ≤ -Real.log (148867 / 500000) ∧
    -Real.log (148867 / 500000) ≤ (1211554809 / 1000000000) := by
  have h := checkLog_sound (w := (101133 / 398867)) (n := 12)
    (lo := (518407627 / 1000000000)) (hi := (129601907 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 148867) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 148867) = 1/(148867 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1211554809 / 1000000000) (-1211554807 / 1000000000) (Real.log (148867 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (451972669 / 1000000000) ≤ -Real.log (1000000 / 1571409) ∧
    -Real.log (1000000 / 1571409) ≤ (45197267 / 100000000) := by
  have h := checkLog_sound (w := (571409 / 2571409)) (n := 12)
    (lo := (451972669 / 1000000000)) (hi := (45197267 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1571409 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1571409 / 1000000) = 1/(1000000 / 1571409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (451972669 / 1000000000) (45197267 / 100000000) (Real.log (1571409 / 1000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1571409 / 1000000) = -Real.log (1000000 / 1571409) := by
    rw [show ((1571409 / 1000000) : ℝ) = ((1000000 / 1571409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (423626097 / 500000000) ≤ -Real.log (428591 / 1000000) ∧
    -Real.log (428591 / 1000000) ≤ (211813049 / 250000000) := by
  have h := checkLog_sound (w := (71409 / 928591)) (n := 12)
    (lo := (77052507 / 500000000)) (hi := (30821003 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 428591) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 428591) = 1/(428591 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-211813049 / 250000000) (-423626097 / 500000000) (Real.log (428591 / 1000000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (453486723 / 1000000000) ≤ -Real.log (100000 / 157379) ∧
    -Real.log (100000 / 157379) ≤ (113371681 / 250000000) := by
  have h := checkLog_sound (w := (57379 / 257379)) (n := 12)
    (lo := (453486723 / 1000000000)) (hi := (113371681 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157379 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157379 / 100000) = 1/(100000 / 157379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (453486723 / 1000000000) (113371681 / 250000000) (Real.log (157379 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157379 / 100000) = -Real.log (100000 / 157379) := by
    rw [show ((157379 / 100000) : ℝ) = ((100000 / 157379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (170564619 / 200000000) ≤ -Real.log (42621 / 100000) ∧
    -Real.log (42621 / 100000) ≤ (852823097 / 1000000000) := by
  have h := checkLog_sound (w := (7379 / 92621)) (n := 12)
    (lo := (31935183 / 200000000)) (hi := (39918979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42621) = 1/(42621 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-852823097 / 1000000000) (-170564619 / 200000000) (Real.log (42621 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1734687331 / 1000000000) ≤ -Real.log (100000000000 / 566715559141) ∧
    -Real.log (100000000000 / 566715559141) ≤ (867343667 / 500000000) := by
  have h := checkLog_sound (w := (166715559141 / 966715559141)) (n := 12)
    (lo := (348392971 / 1000000000)) (hi := (87098243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((566715559141 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(566715559141 / 400000000000) = 1/(100000000000 / 566715559141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1734687331 / 1000000000) (867343667 / 500000000) (Real.log (566715559141 / 100000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (566715559141 / 100000000000) = -Real.log (100000000000 / 566715559141) := by
    rw [show ((566715559141 / 100000000000) : ℝ) = ((100000000000 / 566715559141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (217939389 / 125000000) ≤ -Real.log (7812500000 / 44667230229) ∧
    -Real.log (7812500000 / 44667230229) ≤ (348703023 / 200000000) := by
  have h := checkLog_sound (w := (13417230229 / 75917230229)) (n := 12)
    (lo := (22326297 / 62500000)) (hi := (357220753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((44667230229 / 31250000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(44667230229 / 31250000000) = 1/(7812500000 / 44667230229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (217939389 / 125000000) (348703023 / 200000000) (Real.log (44667230229 / 7812500000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (44667230229 / 7812500000) = -Real.log (7812500000 / 44667230229) := by
    rw [show ((44667230229 / 7812500000) : ℝ) = ((7812500000 / 44667230229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1299224863 / 1000000000) ≤ -Real.log (500000000000 / 1833226782643) ∧
    -Real.log (500000000000 / 1833226782643) ≤ (259844973 / 200000000) := by
  have h := checkLog_sound (w := (833226782643 / 2833226782643)) (n := 12)
    (lo := (606077683 / 1000000000)) (hi := (151519421 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1833226782643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1833226782643 / 1000000000000) = 1/(500000000000 / 1833226782643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1299224863 / 1000000000) (259844973 / 200000000) (Real.log (1833226782643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1833226782643 / 500000000000) = -Real.log (500000000000 / 1833226782643) := by
    rw [show ((1833226782643 / 500000000000) : ℝ) = ((500000000000 / 1833226782643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (653154909 / 500000000) ≤ -Real.log (250000000000 / 923130616363) ∧
    -Real.log (250000000000 / 923130616363) ≤ (65315491 / 50000000) := by
  have h := checkLog_sound (w := (423130616363 / 1423130616363)) (n := 12)
    (lo := (306581319 / 500000000)) (hi := (613162639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((923130616363 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(923130616363 / 500000000000) = 1/(250000000000 / 923130616363) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (653154909 / 500000000) (65315491 / 50000000) (Real.log (923130616363 / 250000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (923130616363 / 250000000000) = -Real.log (250000000000 / 923130616363) := by
    rw [show ((923130616363 / 250000000000) : ℝ) = ((250000000000 / 923130616363) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0040

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0041Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0041
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

theorem reflection_log_1_neg : (381748581 / 1000000000) ≤ -Real.log (256 / 375) ∧
    -Real.log (256 / 375) ≤ (190874291 / 500000000) := by
  have h := checkLog_sound (w := (119 / 631)) (n := 12)
    (lo := (381748581 / 1000000000)) (hi := (190874291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((375 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(375 / 256) = 1/(256 / 375) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (381748581 / 1000000000) (190874291 / 500000000) (Real.log (375 / 256)) := by
  have h := reflection_log_1_neg
  have he : Real.log (375 / 256) = -Real.log (256 / 375) := by
    rw [show ((375 / 256) : ℝ) = ((256 / 375) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (312598259 / 500000000) ≤ -Real.log (137 / 256) ∧
    -Real.log (137 / 256) ≤ (625196519 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 393)) (n := 12)
    (lo := (312598259 / 500000000)) (hi := (625196519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256 / 137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(256 / 137) = 1/(137 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-625196519 / 1000000000) (-312598259 / 500000000) (Real.log (137 / 256)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (380948261 / 1000000000) ≤ -Real.log (2560 / 3747) ∧
    -Real.log (2560 / 3747) ≤ (190474131 / 500000000) := by
  have h := checkLog_sound (w := (1187 / 6307)) (n := 12)
    (lo := (380948261 / 1000000000)) (hi := (190474131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3747 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3747 / 2560) = 1/(2560 / 3747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (380948261 / 1000000000) (190474131 / 500000000) (Real.log (3747 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3747 / 2560) = -Real.log (2560 / 3747) := by
    rw [show ((3747 / 2560) : ℝ) = ((2560 / 3747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (623009131 / 1000000000) ≤ -Real.log (1373 / 2560) ∧
    -Real.log (1373 / 2560) ≤ (155752283 / 250000000) := by
  have h := checkLog_sound (w := (1187 / 3933)) (n := 12)
    (lo := (623009131 / 1000000000)) (hi := (155752283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1373) = 1/(1373 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-155752283 / 250000000) (-623009131 / 1000000000) (Real.log (1373 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (82169759 / 125000000) ≤ -Real.log (128 / 247) ∧
    -Real.log (128 / 247) ≤ (657358073 / 1000000000) := by
  have h := checkLog_sound (w := (119 / 375)) (n := 12)
    (lo := (82169759 / 125000000)) (hi := (657358073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((247 / 128) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(247 / 128) = 1/(128 / 247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (82169759 / 125000000) (657358073 / 1000000000) (Real.log (247 / 128)) := by
  have h := reflection_log_5_neg
  have he : Real.log (247 / 128) = -Real.log (128 / 247) := by
    rw [show ((247 / 128) : ℝ) = ((128 / 247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (663701421 / 250000000) ≤ -Real.log (9 / 128) ∧
    -Real.log (9 / 128) ≤ (331850711 / 125000000) := by
  have h := checkLog_sound (w := (7 / 25)) (n := 12)
    (lo := (35960259 / 62500000)) (hi := (115072829 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16 / 9) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(16 / 9) = 1/(9 / 128) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-331850711 / 125000000) (-663701421 / 250000000) (Real.log (9 / 128)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (105865481 / 200000000) ≤ -Real.log (100000 / 169779) ∧
    -Real.log (100000 / 169779) ≤ (264663703 / 500000000) := by
  have h := checkLog_sound (w := (69779 / 269779)) (n := 12)
    (lo := (105865481 / 200000000)) (hi := (264663703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169779 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169779 / 100000) = 1/(100000 / 169779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (105865481 / 200000000) (264663703 / 500000000) (Real.log (169779 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169779 / 100000) = -Real.log (100000 / 169779) := by
    rw [show ((169779 / 100000) : ℝ) = ((100000 / 169779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (598316569 / 500000000) ≤ -Real.log (30221 / 100000) ∧
    -Real.log (30221 / 100000) ≤ (59831657 / 50000000) := by
  have h := checkLog_sound (w := (19779 / 80221)) (n := 12)
    (lo := (251742979 / 500000000)) (hi := (503485959 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30221) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 30221) = 1/(30221 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-59831657 / 50000000) (-598316569 / 500000000) (Real.log (30221 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (26532089 / 50000000) ≤ -Real.log (1000000 / 1700023) ∧
    -Real.log (1000000 / 1700023) ≤ (530641781 / 1000000000) := by
  have h := checkLog_sound (w := (700023 / 2700023)) (n := 12)
    (lo := (26532089 / 50000000)) (hi := (530641781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1700023 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1700023 / 1000000) = 1/(1000000 / 1700023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (26532089 / 50000000) (530641781 / 1000000000) (Real.log (1700023 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1700023 / 1000000) = -Real.log (1000000 / 1700023) := by
    rw [show ((1700023 / 1000000) : ℝ) = ((1000000 / 1700023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1204049473 / 1000000000) ≤ -Real.log (299977 / 1000000) ∧
    -Real.log (299977 / 1000000) ≤ (48161979 / 40000000) := by
  have h := checkLog_sound (w := (200023 / 799977)) (n := 12)
    (lo := (510902293 / 1000000000)) (hi := (255451147 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 299977) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 299977) = 1/(299977 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48161979 / 40000000) (-1204049473 / 1000000000) (Real.log (299977 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (225234533 / 500000000) ≤ -Real.log (125000 / 196131) ∧
    -Real.log (125000 / 196131) ≤ (450469067 / 1000000000) := by
  have h := checkLog_sound (w := (71131 / 321131)) (n := 12)
    (lo := (225234533 / 500000000)) (hi := (450469067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((196131 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(196131 / 125000) = 1/(125000 / 196131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (225234533 / 500000000) (450469067 / 1000000000) (Real.log (196131 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (196131 / 125000) = -Real.log (125000 / 196131) := by
    rw [show ((196131 / 125000) : ℝ) = ((125000 / 196131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (841758563 / 1000000000) ≤ -Real.log (53869 / 125000) ∧
    -Real.log (53869 / 125000) ≤ (168351713 / 200000000) := by
  have h := checkLog_sound (w := (8631 / 116369)) (n := 12)
    (lo := (148611383 / 1000000000)) (hi := (18576423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 53869) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 53869) = 1/(53869 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-168351713 / 200000000) (-841758563 / 1000000000) (Real.log (53869 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (90394661 / 200000000) ≤ -Real.log (100000 / 157141) ∧
    -Real.log (100000 / 157141) ≤ (225986653 / 500000000) := by
  have h := checkLog_sound (w := (57141 / 257141)) (n := 12)
    (lo := (90394661 / 200000000)) (hi := (225986653 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((157141 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(157141 / 100000) = 1/(100000 / 157141) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (90394661 / 200000000) (225986653 / 500000000) (Real.log (157141 / 100000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (157141 / 100000) = -Real.log (100000 / 157141) := by
    rw [show ((157141 / 100000) : ℝ) = ((100000 / 157141) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (847254527 / 1000000000) ≤ -Real.log (42859 / 100000) ∧
    -Real.log (42859 / 100000) ≤ (847254529 / 1000000000) := by
  have h := checkLog_sound (w := (7141 / 92859)) (n := 12)
    (lo := (154107347 / 1000000000)) (hi := (38526837 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 42859) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 42859) = 1/(42859 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-847254529 / 1000000000) (-847254527 / 1000000000) (Real.log (42859 / 100000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1725960543 / 1000000000) ≤ -Real.log (500000000000 / 2808957347539) ∧
    -Real.log (500000000000 / 2808957347539) ≤ (862980273 / 500000000) := by
  have h := checkLog_sound (w := (808957347539 / 4808957347539)) (n := 12)
    (lo := (339666183 / 1000000000)) (hi := (42458273 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2808957347539 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2808957347539 / 2000000000000) = 1/(500000000000 / 2808957347539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1725960543 / 1000000000) (862980273 / 500000000) (Real.log (2808957347539 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2808957347539 / 500000000000) = -Real.log (500000000000 / 2808957347539) := by
    rw [show ((2808957347539 / 500000000000) : ℝ) = ((500000000000 / 2808957347539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1734691253 / 1000000000) ≤ -Real.log (500000000000 / 2833588908483) ∧
    -Real.log (500000000000 / 2833588908483) ≤ (216836407 / 125000000) := by
  have h := checkLog_sound (w := (833588908483 / 4833588908483)) (n := 12)
    (lo := (348396893 / 1000000000)) (hi := (174198447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2833588908483 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2833588908483 / 2000000000000) = 1/(500000000000 / 2833588908483) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1734691253 / 1000000000) (216836407 / 125000000) (Real.log (2833588908483 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2833588908483 / 500000000000) = -Real.log (500000000000 / 2833588908483) := by
    rw [show ((2833588908483 / 500000000000) : ℝ) = ((500000000000 / 2833588908483) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1292227629 / 1000000000) ≤ -Real.log (500000000000 / 1820444040171) ∧
    -Real.log (500000000000 / 1820444040171) ≤ (1292227631 / 1000000000) := by
  have h := checkLog_sound (w := (820444040171 / 2820444040171)) (n := 12)
    (lo := (599080449 / 1000000000)) (hi := (11981609 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1820444040171 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1820444040171 / 1000000000000) = 1/(500000000000 / 1820444040171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1292227629 / 1000000000) (1292227631 / 1000000000) (Real.log (1820444040171 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1820444040171 / 500000000000) = -Real.log (500000000000 / 1820444040171) := by
    rw [show ((1820444040171 / 500000000000) : ℝ) = ((500000000000 / 1820444040171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (162403479 / 125000000) ≤ -Real.log (125000000000 / 458308056651) ∧
    -Real.log (125000000000 / 458308056651) ≤ (649613917 / 500000000) := by
  have h := checkLog_sound (w := (208308056651 / 708308056651)) (n := 12)
    (lo := (151520163 / 250000000)) (hi := (606080653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((458308056651 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(458308056651 / 250000000000) = 1/(125000000000 / 458308056651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (162403479 / 125000000) (649613917 / 500000000) (Real.log (458308056651 / 125000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (458308056651 / 125000000000) = -Real.log (125000000000 / 458308056651) := by
    rw [show ((458308056651 / 125000000000) : ℝ) = ((125000000000 / 458308056651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0041

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0042Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0042
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

theorem reflection_log_1_neg : (380948261 / 1000000000) ≤ -Real.log (2560 / 3747) ∧
    -Real.log (2560 / 3747) ≤ (190474131 / 500000000) := by
  have h := checkLog_sound (w := (1187 / 6307)) (n := 12)
    (lo := (380948261 / 1000000000)) (hi := (190474131 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3747 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3747 / 2560) = 1/(2560 / 3747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (380948261 / 1000000000) (190474131 / 500000000) (Real.log (3747 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3747 / 2560) = -Real.log (2560 / 3747) := by
    rw [show ((3747 / 2560) : ℝ) = ((2560 / 3747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (623009131 / 1000000000) ≤ -Real.log (1373 / 2560) ∧
    -Real.log (1373 / 2560) ≤ (155752283 / 250000000) := by
  have h := checkLog_sound (w := (1187 / 3933)) (n := 12)
    (lo := (623009131 / 1000000000)) (hi := (155752283 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1373) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1373) = 1/(1373 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-155752283 / 250000000) (-623009131 / 1000000000) (Real.log (1373 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (3801473 / 10000000) ≤ -Real.log (80 / 117) ∧
    -Real.log (80 / 117) ≤ (380147301 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 197)) (n := 12)
    (lo := (3801473 / 10000000)) (hi := (380147301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 80) = 1/(80 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (3801473 / 10000000) (380147301 / 1000000000) (Real.log (117 / 80)) := by
  have h := reflection_log_3_neg
  have he : Real.log (117 / 80) = -Real.log (80 / 117) := by
    rw [show ((117 / 80) : ℝ) = ((80 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (310413259 / 500000000) ≤ -Real.log (43 / 80) ∧
    -Real.log (43 / 80) ≤ (620826519 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 123)) (n := 12)
    (lo := (310413259 / 500000000)) (hi := (620826519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 43) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 43) = 1/(43 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-620826519 / 1000000000) (-310413259 / 500000000) (Real.log (43 / 80)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (656142759 / 1000000000) ≤ -Real.log (1280 / 2467) ∧
    -Real.log (1280 / 2467) ≤ (16403569 / 25000000) := by
  have h := checkLog_sound (w := (1187 / 3747)) (n := 12)
    (lo := (656142759 / 1000000000)) (hi := (16403569 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2467 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2467 / 1280) = 1/(1280 / 2467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (656142759 / 1000000000) (16403569 / 25000000) (Real.log (2467 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2467 / 1280) = -Real.log (1280 / 2467) := by
    rw [show ((2467 / 1280) : ℝ) = ((1280 / 2467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (1311007931 / 500000000) ≤ -Real.log (93 / 1280) ∧
    -Real.log (93 / 1280) ≤ (1311007933 / 500000000) := by
  have h := checkLog_sound (w := (67 / 253)) (n := 12)
    (lo := (271287161 / 500000000)) (hi := (542574323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 93) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 93) = 1/(93 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-1311007933 / 500000000) (-1311007931 / 500000000) (Real.log (93 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (654925967 / 1000000000) ≤ -Real.log (40 / 77) ∧
    -Real.log (40 / 77) ≤ (40932873 / 62500000) := by
  have h := checkLog_sound (w := (37 / 117)) (n := 12)
    (lo := (654925967 / 1000000000)) (hi := (40932873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77 / 40) = 1/(40 / 77) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (654925967 / 1000000000) (40932873 / 62500000) (Real.log (77 / 40)) := by
  have h := reflection_log_7_neg
  have he : Real.log (77 / 40) = -Real.log (40 / 77) := by
    rw [show ((77 / 40) : ℝ) = ((40 / 77) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2590267163 / 1000000000) ≤ -Real.log (3 / 40) ∧
    -Real.log (3 / 40) ≤ (2590267167 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5 / 3) = 1/(3 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2590267167 / 1000000000) (-2590267163 / 1000000000) (Real.log (3 / 40)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (528018967 / 1000000000) ≤ -Real.log (100000 / 169557) ∧
    -Real.log (100000 / 169557) ≤ (66002371 / 125000000) := by
  have h := checkLog_sound (w := (69557 / 269557)) (n := 12)
    (lo := (528018967 / 1000000000)) (hi := (66002371 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169557 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169557 / 100000) = 1/(100000 / 169557) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (528018967 / 1000000000) (66002371 / 125000000) (Real.log (169557 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (169557 / 100000) = -Real.log (100000 / 169557) := by
    rw [show ((169557 / 100000) : ℝ) = ((100000 / 169557) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (594657051 / 500000000) ≤ -Real.log (30443 / 100000) ∧
    -Real.log (30443 / 100000) ≤ (148664263 / 125000000) := by
  have h := checkLog_sound (w := (19557 / 80443)) (n := 12)
    (lo := (248083461 / 500000000)) (hi := (496166923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 30443) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 30443) = 1/(30443 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-148664263 / 125000000) (-594657051 / 500000000) (Real.log (30443 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (264663997 / 500000000) ≤ -Real.log (1000000 / 1697791) ∧
    -Real.log (1000000 / 1697791) ≤ (105865599 / 200000000) := by
  have h := checkLog_sound (w := (697791 / 2697791)) (n := 12)
    (lo := (264663997 / 500000000)) (hi := (105865599 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1697791 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1697791 / 1000000) = 1/(1000000 / 1697791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (264663997 / 500000000) (105865599 / 200000000) (Real.log (1697791 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1697791 / 1000000) = -Real.log (1000000 / 1697791) := by
    rw [show ((1697791 / 1000000) : ℝ) = ((1000000 / 1697791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1196636447 / 1000000000) ≤ -Real.log (302209 / 1000000) ∧
    -Real.log (302209 / 1000000) ≤ (1196636449 / 1000000000) := by
  have h := checkLog_sound (w := (197791 / 802209)) (n := 12)
    (lo := (503489267 / 1000000000)) (hi := (125872317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 302209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 302209) = 1/(302209 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1196636449 / 1000000000) (-1196636447 / 1000000000) (Real.log (302209 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (448974049 / 1000000000) ≤ -Real.log (62500 / 97919) ∧
    -Real.log (62500 / 97919) ≤ (8979481 / 20000000) := by
  have h := checkLog_sound (w := (35419 / 160419)) (n := 12)
    (lo := (448974049 / 1000000000)) (hi := (8979481 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97919 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97919 / 62500) = 1/(62500 / 97919) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (448974049 / 1000000000) (8979481 / 20000000) (Real.log (97919 / 62500)) := by
  have h := reflection_log_13_neg
  have he : Real.log (97919 / 62500) = -Real.log (62500 / 97919) := by
    rw [show ((97919 / 62500) : ℝ) = ((62500 / 97919) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (836334181 / 1000000000) ≤ -Real.log (27081 / 62500) ∧
    -Real.log (27081 / 62500) ≤ (836334183 / 1000000000) := by
  have h := checkLog_sound (w := (4169 / 58331)) (n := 12)
    (lo := (143187001 / 1000000000)) (hi := (71593501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27081) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 27081) = 1/(27081 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-836334183 / 1000000000) (-836334181 / 1000000000) (Real.log (27081 / 62500)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (450469703 / 1000000000) ≤ -Real.log (1000000 / 1569049) ∧
    -Real.log (1000000 / 1569049) ≤ (56308713 / 125000000) := by
  have h := checkLog_sound (w := (569049 / 2569049)) (n := 12)
    (lo := (450469703 / 1000000000)) (hi := (56308713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1569049 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1569049 / 1000000) = 1/(1000000 / 1569049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (450469703 / 1000000000) (56308713 / 125000000) (Real.log (1569049 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1569049 / 1000000) = -Real.log (1000000 / 1569049) := by
    rw [show ((1569049 / 1000000) : ℝ) = ((1000000 / 1569049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (841760883 / 1000000000) ≤ -Real.log (430951 / 1000000) ∧
    -Real.log (430951 / 1000000) ≤ (168352177 / 200000000) := by
  have h := checkLog_sound (w := (69049 / 930951)) (n := 12)
    (lo := (148613703 / 1000000000)) (hi := (18576713 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 430951) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 430951) = 1/(430951 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-168352177 / 200000000) (-841760883 / 1000000000) (Real.log (430951 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1717333069 / 1000000000) ≤ -Real.log (500000000000 / 2784827382321) ∧
    -Real.log (500000000000 / 2784827382321) ≤ (107333317 / 62500000) := by
  have h := checkLog_sound (w := (784827382321 / 4784827382321)) (n := 12)
    (lo := (331038709 / 1000000000)) (hi := (33103871 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2784827382321 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2784827382321 / 2000000000000) = 1/(500000000000 / 2784827382321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1717333069 / 1000000000) (107333317 / 62500000) (Real.log (2784827382321 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2784827382321 / 500000000000) = -Real.log (500000000000 / 2784827382321) := by
    rw [show ((2784827382321 / 500000000000) : ℝ) = ((500000000000 / 2784827382321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1725964441 / 1000000000) ≤ -Real.log (20000000000 / 112358731871) ∧
    -Real.log (20000000000 / 112358731871) ≤ (431491111 / 250000000) := by
  have h := checkLog_sound (w := (32358731871 / 192358731871)) (n := 12)
    (lo := (339670081 / 1000000000)) (hi := (169835041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112358731871 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(112358731871 / 80000000000) = 1/(20000000000 / 112358731871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1725964441 / 1000000000) (431491111 / 250000000) (Real.log (112358731871 / 20000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (112358731871 / 20000000000) = -Real.log (20000000000 / 112358731871) := by
    rw [show ((112358731871 / 20000000000) : ℝ) = ((20000000000 / 112358731871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (128530823 / 100000000) ≤ -Real.log (50000000000 / 180789114139) ∧
    -Real.log (50000000000 / 180789114139) ≤ (160663529 / 125000000) := by
  have h := checkLog_sound (w := (80789114139 / 280789114139)) (n := 12)
    (lo := (11843221 / 20000000)) (hi := (592161051 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180789114139 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(180789114139 / 100000000000) = 1/(50000000000 / 180789114139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (128530823 / 100000000) (160663529 / 125000000) (Real.log (180789114139 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (180789114139 / 50000000000) = -Real.log (50000000000 / 180789114139) := by
    rw [show ((180789114139 / 50000000000) : ℝ) = ((50000000000 / 180789114139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1292230587 / 1000000000) ≤ -Real.log (100000000000 / 364089884929) ∧
    -Real.log (100000000000 / 364089884929) ≤ (1292230589 / 1000000000) := by
  have h := checkLog_sound (w := (164089884929 / 564089884929)) (n := 12)
    (lo := (599083407 / 1000000000)) (hi := (37442713 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((364089884929 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(364089884929 / 200000000000) = 1/(100000000000 / 364089884929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1292230587 / 1000000000) (1292230589 / 1000000000) (Real.log (364089884929 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (364089884929 / 100000000000) = -Real.log (100000000000 / 364089884929) := by
    rw [show ((364089884929 / 100000000000) : ℝ) = ((100000000000 / 364089884929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0042

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0043Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0043
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

theorem reflection_log_1_neg : (3801473 / 10000000) ≤ -Real.log (80 / 117) ∧
    -Real.log (80 / 117) ≤ (380147301 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 197)) (n := 12)
    (lo := (3801473 / 10000000)) (hi := (380147301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117 / 80) = 1/(80 / 117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (3801473 / 10000000) (380147301 / 1000000000) (Real.log (117 / 80)) := by
  have h := reflection_log_1_neg
  have he : Real.log (117 / 80) = -Real.log (80 / 117) := by
    rw [show ((117 / 80) : ℝ) = ((80 / 117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (310413259 / 500000000) ≤ -Real.log (43 / 80) ∧
    -Real.log (43 / 80) ≤ (620826519 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 123)) (n := 12)
    (lo := (310413259 / 500000000)) (hi := (620826519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 43) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 43) = 1/(43 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-620826519 / 1000000000) (-310413259 / 500000000) (Real.log (43 / 80)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11854553 / 31250000) ≤ -Real.log (2560 / 3741) ∧
    -Real.log (2560 / 3741) ≤ (379345697 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 6301)) (n := 12)
    (lo := (11854553 / 31250000)) (hi := (379345697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 2560) = 1/(2560 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11854553 / 31250000) (379345697 / 1000000000) (Real.log (3741 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3741 / 2560) = -Real.log (2560 / 3741) := by
    rw [show ((3741 / 2560) : ℝ) = ((2560 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (618648659 / 1000000000) ≤ -Real.log (1379 / 2560) ∧
    -Real.log (1379 / 2560) ≤ (30932433 / 50000000) := by
  have h := checkLog_sound (w := (1181 / 3939)) (n := 12)
    (lo := (618648659 / 1000000000)) (hi := (30932433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1379) = 1/(1379 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-30932433 / 50000000) (-618648659 / 1000000000) (Real.log (1379 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (654925967 / 1000000000) ≤ -Real.log (40 / 77) ∧
    -Real.log (40 / 77) ≤ (40932873 / 62500000) := by
  have h := checkLog_sound (w := (37 / 117)) (n := 12)
    (lo := (654925967 / 1000000000)) (hi := (40932873 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77 / 40) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77 / 40) = 1/(40 / 77) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (654925967 / 1000000000) (40932873 / 62500000) (Real.log (77 / 40)) := by
  have h := reflection_log_5_neg
  have he : Real.log (77 / 40) = -Real.log (40 / 77) := by
    rw [show ((77 / 40) : ℝ) = ((40 / 77) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2590267163 / 1000000000) ≤ -Real.log (3 / 40) ∧
    -Real.log (3 / 40) ≤ (2590267167 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 4)) (n := 12)
    (lo := (510825623 / 1000000000)) (hi := (63853203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5 / 3) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(5 / 3) = 1/(3 / 40) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2590267167 / 1000000000) (-2590267163 / 1000000000) (Real.log (3 / 40)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (653707693 / 1000000000) ≤ -Real.log (1280 / 2461) ∧
    -Real.log (1280 / 2461) ≤ (326853847 / 500000000) := by
  have h := checkLog_sound (w := (1181 / 3741)) (n := 12)
    (lo := (653707693 / 1000000000)) (hi := (326853847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1280) = 1/(1280 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (653707693 / 1000000000) (326853847 / 500000000) (Real.log (2461 / 1280)) := by
  have h := reflection_log_7_neg
  have he : Real.log (2461 / 1280) = -Real.log (1280 / 2461) := by
    rw [show ((2461 / 1280) : ℝ) = ((1280 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (511899101 / 200000000) ≤ -Real.log (99 / 1280) ∧
    -Real.log (99 / 1280) ≤ (2559495509 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 99) = 1/(99 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2559495509 / 1000000000) (-511899101 / 200000000) (Real.log (99 / 1280)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (526715311 / 1000000000) ≤ -Real.log (1000000 / 1693361) ∧
    -Real.log (1000000 / 1693361) ≤ (32919707 / 62500000) := by
  have h := checkLog_sound (w := (693361 / 2693361)) (n := 12)
    (lo := (526715311 / 1000000000)) (hi := (32919707 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1693361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1693361 / 1000000) = 1/(1000000 / 1693361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (526715311 / 1000000000) (32919707 / 62500000) (Real.log (1693361 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1693361 / 1000000) = -Real.log (1000000 / 1693361) := by
    rw [show ((1693361 / 1000000) : ℝ) = ((1000000 / 1693361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (591042059 / 500000000) ≤ -Real.log (306639 / 1000000) ∧
    -Real.log (306639 / 1000000) ≤ (29552103 / 25000000) := by
  have h := checkLog_sound (w := (193361 / 806639)) (n := 12)
    (lo := (244468469 / 500000000)) (hi := (488936939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 306639) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 306639) = 1/(306639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-29552103 / 25000000) (-591042059 / 500000000) (Real.log (306639 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (528019557 / 1000000000) ≤ -Real.log (1000000 / 1695571) ∧
    -Real.log (1000000 / 1695571) ≤ (264009779 / 500000000) := by
  have h := checkLog_sound (w := (695571 / 2695571)) (n := 12)
    (lo := (528019557 / 1000000000)) (hi := (264009779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1695571 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1695571 / 1000000) = 1/(1000000 / 1695571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (528019557 / 1000000000) (264009779 / 500000000) (Real.log (1695571 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1695571 / 1000000) = -Real.log (1000000 / 1695571) := by
    rw [show ((1695571 / 1000000) : ℝ) = ((1000000 / 1695571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1189317387 / 1000000000) ≤ -Real.log (304429 / 1000000) ∧
    -Real.log (304429 / 1000000) ≤ (1189317389 / 1000000000) := by
  have h := checkLog_sound (w := (195571 / 804429)) (n := 12)
    (lo := (496170207 / 1000000000)) (hi := (15505319 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 304429) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 304429) = 1/(304429 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1189317389 / 1000000000) (-1189317387 / 1000000000) (Real.log (304429 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (4474883 / 10000000) ≤ -Real.log (500000 / 782189) ∧
    -Real.log (500000 / 782189) ≤ (447488301 / 1000000000) := by
  have h := checkLog_sound (w := (282189 / 1282189)) (n := 12)
    (lo := (4474883 / 10000000)) (hi := (447488301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((782189 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(782189 / 500000) = 1/(500000 / 782189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (4474883 / 10000000) (447488301 / 1000000000) (Real.log (782189 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (782189 / 500000) = -Real.log (500000 / 782189) := by
    rw [show ((782189 / 500000) : ℝ) = ((500000 / 782189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (830980383 / 1000000000) ≤ -Real.log (217811 / 500000) ∧
    -Real.log (217811 / 500000) ≤ (166196077 / 200000000) := by
  have h := checkLog_sound (w := (32189 / 467811)) (n := 12)
    (lo := (137833203 / 1000000000)) (hi := (34458301 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 217811) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 217811) = 1/(217811 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-166196077 / 200000000) (-830980383 / 1000000000) (Real.log (217811 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (448974687 / 1000000000) ≤ -Real.log (200000 / 313341) ∧
    -Real.log (200000 / 313341) ≤ (14030459 / 31250000) := by
  have h := checkLog_sound (w := (113341 / 513341)) (n := 12)
    (lo := (448974687 / 1000000000)) (hi := (14030459 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((313341 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(313341 / 200000) = 1/(200000 / 313341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (448974687 / 1000000000) (14030459 / 31250000) (Real.log (313341 / 200000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (313341 / 200000) = -Real.log (200000 / 313341) := by
    rw [show ((313341 / 200000) : ℝ) = ((200000 / 313341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (836336489 / 1000000000) ≤ -Real.log (86659 / 200000) ∧
    -Real.log (86659 / 200000) ≤ (836336491 / 1000000000) := by
  have h := checkLog_sound (w := (13341 / 186659)) (n := 12)
    (lo := (143189309 / 1000000000)) (hi := (14318931 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 86659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 86659) = 1/(86659 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-836336491 / 1000000000) (-836336489 / 1000000000) (Real.log (86659 / 200000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1708799429 / 1000000000) ≤ -Real.log (250000000000 / 1380581889453) ∧
    -Real.log (250000000000 / 1380581889453) ≤ (213599929 / 125000000) := by
  have h := checkLog_sound (w := (380581889453 / 2380581889453)) (n := 12)
    (lo := (322505069 / 1000000000)) (hi := (32250507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1380581889453 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1380581889453 / 1000000000000) = 1/(250000000000 / 1380581889453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1708799429 / 1000000000) (213599929 / 125000000) (Real.log (1380581889453 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (1380581889453 / 250000000000) = -Real.log (250000000000 / 1380581889453) := by
    rw [show ((1380581889453 / 250000000000) : ℝ) = ((250000000000 / 1380581889453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (107333559 / 62500000) ≤ -Real.log (15625000000 / 87026192889) ∧
    -Real.log (15625000000 / 87026192889) ≤ (1717336947 / 1000000000) := by
  have h := checkLog_sound (w := (24526192889 / 149526192889)) (n := 12)
    (lo := (41380323 / 125000000)) (hi := (66208517 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((87026192889 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(87026192889 / 62500000000) = 1/(15625000000 / 87026192889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (107333559 / 62500000) (1717336947 / 1000000000) (Real.log (87026192889 / 15625000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (87026192889 / 15625000000) = -Real.log (15625000000 / 87026192889) := by
    rw [show ((87026192889 / 15625000000) : ℝ) = ((15625000000 / 87026192889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (319617171 / 250000000) ≤ -Real.log (500000000000 / 1795568176079) ∧
    -Real.log (500000000000 / 1795568176079) ≤ (639234343 / 500000000) := by
  have h := checkLog_sound (w := (795568176079 / 2795568176079)) (n := 12)
    (lo := (18291297 / 31250000)) (hi := (117064301 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1795568176079 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1795568176079 / 1000000000000) = 1/(500000000000 / 1795568176079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (319617171 / 250000000) (639234343 / 500000000) (Real.log (1795568176079 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1795568176079 / 500000000000) = -Real.log (500000000000 / 1795568176079) := by
    rw [show ((1795568176079 / 500000000000) : ℝ) = ((500000000000 / 1795568176079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (160663897 / 125000000) ≤ -Real.log (100000000000 / 361579293553) ∧
    -Real.log (100000000000 / 361579293553) ≤ (642655589 / 500000000) := by
  have h := checkLog_sound (w := (161579293553 / 561579293553)) (n := 12)
    (lo := (148040999 / 250000000)) (hi := (592163997 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361579293553 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(361579293553 / 200000000000) = 1/(100000000000 / 361579293553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (160663897 / 125000000) (642655589 / 500000000) (Real.log (361579293553 / 100000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (361579293553 / 100000000000) = -Real.log (100000000000 / 361579293553) := by
    rw [show ((361579293553 / 100000000000) : ℝ) = ((100000000000 / 361579293553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0043

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0044Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0044
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

theorem reflection_log_1_neg : (11854553 / 31250000) ≤ -Real.log (2560 / 3741) ∧
    -Real.log (2560 / 3741) ≤ (379345697 / 1000000000) := by
  have h := checkLog_sound (w := (1181 / 6301)) (n := 12)
    (lo := (11854553 / 31250000)) (hi := (379345697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3741 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3741 / 2560) = 1/(2560 / 3741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11854553 / 31250000) (379345697 / 1000000000) (Real.log (3741 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3741 / 2560) = -Real.log (2560 / 3741) := by
    rw [show ((3741 / 2560) : ℝ) = ((2560 / 3741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (618648659 / 1000000000) ≤ -Real.log (1379 / 2560) ∧
    -Real.log (1379 / 2560) ≤ (30932433 / 50000000) := by
  have h := checkLog_sound (w := (1181 / 3939)) (n := 12)
    (lo := (618648659 / 1000000000)) (hi := (30932433 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1379) = 1/(1379 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-30932433 / 50000000) (-618648659 / 1000000000) (Real.log (1379 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (7570869 / 20000000) ≤ -Real.log (1280 / 1869) ∧
    -Real.log (1280 / 1869) ≤ (378543451 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 3149)) (n := 12)
    (lo := (7570869 / 20000000)) (hi := (378543451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1280) = 1/(1280 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (7570869 / 20000000) (378543451 / 1000000000) (Real.log (1869 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1869 / 1280) = -Real.log (1280 / 1869) := by
    rw [show ((1869 / 1280) : ℝ) = ((1280 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (616475533 / 1000000000) ≤ -Real.log (691 / 1280) ∧
    -Real.log (691 / 1280) ≤ (308237767 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1971)) (n := 12)
    (lo := (616475533 / 1000000000)) (hi := (308237767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 691) = 1/(691 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-308237767 / 500000000) (-616475533 / 1000000000) (Real.log (691 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (653707693 / 1000000000) ≤ -Real.log (1280 / 2461) ∧
    -Real.log (1280 / 2461) ≤ (326853847 / 500000000) := by
  have h := checkLog_sound (w := (1181 / 3741)) (n := 12)
    (lo := (653707693 / 1000000000)) (hi := (326853847 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2461 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2461 / 1280) = 1/(1280 / 2461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (653707693 / 1000000000) (326853847 / 500000000) (Real.log (2461 / 1280)) := by
  have h := reflection_log_5_neg
  have he : Real.log (2461 / 1280) = -Real.log (1280 / 2461) := by
    rw [show ((2461 / 1280) : ℝ) = ((1280 / 2461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (511899101 / 200000000) ≤ -Real.log (99 / 1280) ∧
    -Real.log (99 / 1280) ≤ (2559495509 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 259)) (n := 12)
    (lo := (96010793 / 200000000)) (hi := (240026983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((160 / 99) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(160 / 99) = 1/(99 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2559495509 / 1000000000) (-511899101 / 200000000) (Real.log (99 / 1280)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (652487933 / 1000000000) ≤ -Real.log (640 / 1229) ∧
    -Real.log (640 / 1229) ≤ (326243967 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1869)) (n := 12)
    (lo := (652487933 / 1000000000)) (hi := (326243967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 640) = 1/(640 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (652487933 / 1000000000) (326243967 / 500000000) (Real.log (1229 / 640)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1229 / 640) = -Real.log (640 / 1229) := by
    rw [show ((1229 / 640) : ℝ) = ((640 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (2529642541 / 1000000000) ≤ -Real.log (51 / 640) ∧
    -Real.log (51 / 640) ≤ (505928509 / 200000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 51) = 1/(51 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-505928509 / 200000000) (-2529642541 / 1000000000) (Real.log (51 / 640)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (525416457 / 1000000000) ≤ -Real.log (1000000 / 1691163) ∧
    -Real.log (1000000 / 1691163) ≤ (262708229 / 500000000) := by
  have h := checkLog_sound (w := (691163 / 2691163)) (n := 12)
    (lo := (525416457 / 1000000000)) (hi := (262708229 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1691163 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1691163 / 1000000) = 1/(1000000 / 1691163) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (525416457 / 1000000000) (262708229 / 500000000) (Real.log (1691163 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1691163 / 1000000) = -Real.log (1000000 / 1691163) := by
    rw [show ((1691163 / 1000000) : ℝ) = ((1000000 / 1691163) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (73433853 / 62500000) ≤ -Real.log (308837 / 1000000) ∧
    -Real.log (308837 / 1000000) ≤ (23498833 / 20000000) := by
  have h := checkLog_sound (w := (191163 / 808837)) (n := 12)
    (lo := (120448617 / 250000000)) (hi := (481794469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 308837) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 308837) = 1/(308837 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-23498833 / 20000000) (-73433853 / 62500000) (Real.log (308837 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (526715901 / 1000000000) ≤ -Real.log (500000 / 846681) ∧
    -Real.log (500000 / 846681) ≤ (263357951 / 500000000) := by
  have h := checkLog_sound (w := (346681 / 1346681)) (n := 12)
    (lo := (526715901 / 1000000000)) (hi := (263357951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((846681 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(846681 / 500000) = 1/(500000 / 846681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (526715901 / 1000000000) (263357951 / 500000000) (Real.log (846681 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (846681 / 500000) = -Real.log (500000 / 846681) := by
    rw [show ((846681 / 500000) : ℝ) = ((500000 / 846681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1182087379 / 1000000000) ≤ -Real.log (153319 / 500000) ∧
    -Real.log (153319 / 500000) ≤ (1182087381 / 1000000000) := by
  have h := checkLog_sound (w := (96681 / 403319)) (n := 12)
    (lo := (488940199 / 1000000000)) (hi := (2444701 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 153319) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 153319) = 1/(153319 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-1182087381 / 1000000000) (-1182087379 / 1000000000) (Real.log (153319 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (55751323 / 125000000) ≤ -Real.log (250000 / 390517) ∧
    -Real.log (250000 / 390517) ≤ (89202117 / 200000000) := by
  have h := checkLog_sound (w := (140517 / 640517)) (n := 12)
    (lo := (55751323 / 125000000)) (hi := (89202117 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((390517 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(390517 / 250000) = 1/(250000 / 390517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (55751323 / 125000000) (89202117 / 200000000) (Real.log (390517 / 250000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (390517 / 250000) = -Real.log (250000 / 390517) := by
    rw [show ((390517 / 250000) : ℝ) = ((250000 / 390517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (825691631 / 1000000000) ≤ -Real.log (109483 / 250000) ∧
    -Real.log (109483 / 250000) ≤ (825691633 / 1000000000) := by
  have h := checkLog_sound (w := (15517 / 234483)) (n := 12)
    (lo := (132544451 / 1000000000)) (hi := (33136113 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 109483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 109483) = 1/(109483 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-825691633 / 1000000000) (-825691631 / 1000000000) (Real.log (109483 / 250000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22374447 / 50000000) ≤ -Real.log (1000000 / 1564379) ∧
    -Real.log (1000000 / 1564379) ≤ (447488941 / 1000000000) := by
  have h := checkLog_sound (w := (564379 / 2564379)) (n := 12)
    (lo := (22374447 / 50000000)) (hi := (447488941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1564379 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1564379 / 1000000) = 1/(1000000 / 1564379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22374447 / 50000000) (447488941 / 1000000000) (Real.log (1564379 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1564379 / 1000000) = -Real.log (1000000 / 1564379) := by
    rw [show ((1564379 / 1000000) : ℝ) = ((1000000 / 1564379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (830982679 / 1000000000) ≤ -Real.log (435621 / 1000000) ∧
    -Real.log (435621 / 1000000) ≤ (830982681 / 1000000000) := by
  have h := checkLog_sound (w := (64379 / 935621)) (n := 12)
    (lo := (137835499 / 1000000000)) (hi := (275671 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 435621) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 435621) = 1/(435621 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-830982681 / 1000000000) (-830982679 / 1000000000) (Real.log (435621 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (850179053 / 500000000) ≤ -Real.log (4000000000 / 21903632013) ∧
    -Real.log (4000000000 / 21903632013) ≤ (1700358109 / 1000000000) := by
  have h := checkLog_sound (w := (5903632013 / 37903632013)) (n := 12)
    (lo := (157031873 / 500000000)) (hi := (314063747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21903632013 / 16000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(21903632013 / 16000000000) = 1/(4000000000 / 21903632013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (850179053 / 500000000) (1700358109 / 1000000000) (Real.log (21903632013 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (21903632013 / 4000000000) = -Real.log (4000000000 / 21903632013) := by
    rw [show ((21903632013 / 4000000000) : ℝ) = ((4000000000 / 21903632013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (1708803281 / 1000000000) ≤ -Real.log (500000000000 / 2761174414131) ∧
    -Real.log (500000000000 / 2761174414131) ≤ (427200821 / 250000000) := by
  have h := checkLog_sound (w := (761174414131 / 4761174414131)) (n := 12)
    (lo := (322508921 / 1000000000)) (hi := (161254461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2761174414131 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2761174414131 / 2000000000000) = 1/(500000000000 / 2761174414131) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (1708803281 / 1000000000) (427200821 / 250000000) (Real.log (2761174414131 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2761174414131 / 500000000000) = -Real.log (500000000000 / 2761174414131) := by
    rw [show ((2761174414131 / 500000000000) : ℝ) = ((500000000000 / 2761174414131) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (254340443 / 200000000) ≤ -Real.log (50000000000 / 178345953253) ∧
    -Real.log (50000000000 / 178345953253) ≤ (1271702217 / 1000000000) := by
  have h := checkLog_sound (w := (78345953253 / 278345953253)) (n := 12)
    (lo := (115711007 / 200000000)) (hi := (144638759 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178345953253 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(178345953253 / 100000000000) = 1/(50000000000 / 178345953253) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (254340443 / 200000000) (1271702217 / 1000000000) (Real.log (178345953253 / 50000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (178345953253 / 50000000000) = -Real.log (50000000000 / 178345953253) := by
    rw [show ((178345953253 / 50000000000) : ℝ) = ((50000000000 / 178345953253) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1278471619 / 1000000000) ≤ -Real.log (20000000000 / 71822937829) ∧
    -Real.log (20000000000 / 71822937829) ≤ (1278471621 / 1000000000) := by
  have h := checkLog_sound (w := (31822937829 / 111822937829)) (n := 12)
    (lo := (585324439 / 1000000000)) (hi := (14633111 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71822937829 / 40000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(71822937829 / 40000000000) = 1/(20000000000 / 71822937829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1278471619 / 1000000000) (1278471621 / 1000000000) (Real.log (71822937829 / 20000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (71822937829 / 20000000000) = -Real.log (20000000000 / 71822937829) := by
    rw [show ((71822937829 / 20000000000) : ℝ) = ((20000000000 / 71822937829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0044

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0045Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0045
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

theorem reflection_log_1_neg : (7570869 / 20000000) ≤ -Real.log (1280 / 1869) ∧
    -Real.log (1280 / 1869) ≤ (378543451 / 1000000000) := by
  have h := checkLog_sound (w := (589 / 3149)) (n := 12)
    (lo := (7570869 / 20000000)) (hi := (378543451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1869 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1869 / 1280) = 1/(1280 / 1869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (7570869 / 20000000) (378543451 / 1000000000) (Real.log (1869 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1869 / 1280) = -Real.log (1280 / 1869) := by
    rw [show ((1869 / 1280) : ℝ) = ((1280 / 1869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (616475533 / 1000000000) ≤ -Real.log (691 / 1280) ∧
    -Real.log (691 / 1280) ≤ (308237767 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1971)) (n := 12)
    (lo := (616475533 / 1000000000)) (hi := (308237767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 691) = 1/(691 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-308237767 / 500000000) (-616475533 / 1000000000) (Real.log (691 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (4721757 / 12500000) ≤ -Real.log (512 / 747) ∧
    -Real.log (512 / 747) ≤ (377740561 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 1259)) (n := 12)
    (lo := (4721757 / 12500000)) (hi := (377740561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 512) = 1/(512 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (4721757 / 12500000) (377740561 / 1000000000) (Real.log (747 / 512)) := by
  have h := reflection_log_3_neg
  have he : Real.log (747 / 512) = -Real.log (512 / 747) := by
    rw [show ((747 / 512) : ℝ) = ((512 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (307153559 / 500000000) ≤ -Real.log (277 / 512) ∧
    -Real.log (277 / 512) ≤ (614307119 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 789)) (n := 12)
    (lo := (307153559 / 500000000)) (hi := (614307119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 277) = 1/(277 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-614307119 / 1000000000) (-307153559 / 500000000) (Real.log (277 / 512)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (652487933 / 1000000000) ≤ -Real.log (640 / 1229) ∧
    -Real.log (640 / 1229) ≤ (326243967 / 500000000) := by
  have h := checkLog_sound (w := (589 / 1869)) (n := 12)
    (lo := (652487933 / 1000000000)) (hi := (326243967 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1229 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1229 / 640) = 1/(640 / 1229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (652487933 / 1000000000) (326243967 / 500000000) (Real.log (1229 / 640)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1229 / 640) = -Real.log (640 / 1229) := by
    rw [show ((1229 / 640) : ℝ) = ((640 / 1229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (2529642541 / 1000000000) ≤ -Real.log (51 / 640) ∧
    -Real.log (51 / 640) ≤ (505928509 / 200000000) := by
  have h := checkLog_sound (w := (29 / 131)) (n := 12)
    (lo := (450201001 / 1000000000)) (hi := (225100501 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 51) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(80 / 51) = 1/(51 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-505928509 / 200000000) (-2529642541 / 1000000000) (Real.log (51 / 640)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (651266683 / 1000000000) ≤ -Real.log (256 / 491) ∧
    -Real.log (256 / 491) ≤ (162816671 / 250000000) := by
  have h := checkLog_sound (w := (235 / 747)) (n := 12)
    (lo := (651266683 / 1000000000)) (hi := (162816671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 256) = 1/(256 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (651266683 / 1000000000) (162816671 / 250000000) (Real.log (491 / 256)) := by
  have h := reflection_log_7_neg
  have he : Real.log (491 / 256) = -Real.log (256 / 491) := by
    rw [show ((491 / 256) : ℝ) = ((256 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (500131001 / 200000000) ≤ -Real.log (21 / 256) ∧
    -Real.log (21 / 256) ≤ (2500655009 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 21) = 1/(21 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-2500655009 / 1000000000) (-500131001 / 200000000) (Real.log (21 / 256)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (131030459 / 250000000) ≤ -Real.log (40000 / 67559) ∧
    -Real.log (40000 / 67559) ≤ (524121837 / 1000000000) := by
  have h := checkLog_sound (w := (27559 / 107559)) (n := 12)
    (lo := (131030459 / 250000000)) (hi := (524121837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67559 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67559 / 40000) = 1/(40000 / 67559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (131030459 / 250000000) (524121837 / 1000000000) (Real.log (67559 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (67559 / 40000) = -Real.log (40000 / 67559) := by
    rw [show ((67559 / 40000) : ℝ) = ((40000 / 67559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (1167881983 / 1000000000) ≤ -Real.log (12441 / 40000) ∧
    -Real.log (12441 / 40000) ≤ (233576397 / 200000000) := by
  have h := checkLog_sound (w := (7559 / 32441)) (n := 12)
    (lo := (474734803 / 1000000000)) (hi := (118683701 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 12441) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 12441) = 1/(12441 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-233576397 / 200000000) (-1167881983 / 1000000000) (Real.log (12441 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (525417049 / 1000000000) ≤ -Real.log (250000 / 422791) ∧
    -Real.log (250000 / 422791) ≤ (10508341 / 20000000) := by
  have h := checkLog_sound (w := (172791 / 672791)) (n := 12)
    (lo := (525417049 / 1000000000)) (hi := (10508341 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((422791 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(422791 / 250000) = 1/(250000 / 422791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (525417049 / 1000000000) (10508341 / 20000000) (Real.log (422791 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (422791 / 250000) = -Real.log (250000 / 422791) := by
    rw [show ((422791 / 250000) : ℝ) = ((250000 / 422791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (587472443 / 500000000) ≤ -Real.log (77209 / 250000) ∧
    -Real.log (77209 / 250000) ≤ (146868111 / 125000000) := by
  have h := checkLog_sound (w := (47791 / 202209)) (n := 12)
    (lo := (240898853 / 500000000)) (hi := (481797707 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 77209) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 77209) = 1/(77209 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-146868111 / 125000000) (-587472443 / 500000000) (Real.log (77209 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (222270469 / 500000000) ≤ -Real.log (500000 / 779887) ∧
    -Real.log (500000 / 779887) ≤ (444540939 / 1000000000) := by
  have h := checkLog_sound (w := (279887 / 1279887)) (n := 12)
    (lo := (222270469 / 500000000)) (hi := (444540939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((779887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(779887 / 500000) = 1/(500000 / 779887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (222270469 / 500000000) (444540939 / 1000000000) (Real.log (779887 / 500000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (779887 / 500000) = -Real.log (500000 / 779887) := by
    rw [show ((779887 / 500000) : ℝ) = ((500000 / 779887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (820467047 / 1000000000) ≤ -Real.log (220113 / 500000) ∧
    -Real.log (220113 / 500000) ≤ (820467049 / 1000000000) := by
  have h := checkLog_sound (w := (29887 / 470113)) (n := 12)
    (lo := (127319867 / 1000000000)) (hi := (31829967 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 220113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 220113) = 1/(220113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-820467049 / 1000000000) (-820467047 / 1000000000) (Real.log (220113 / 500000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (55751403 / 125000000) ≤ -Real.log (1000000 / 1562069) ∧
    -Real.log (1000000 / 1562069) ≤ (17840449 / 40000000) := by
  have h := checkLog_sound (w := (562069 / 2562069)) (n := 12)
    (lo := (55751403 / 125000000)) (hi := (17840449 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1562069 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1562069 / 1000000) = 1/(1000000 / 1562069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (55751403 / 125000000) (17840449 / 40000000) (Real.log (1562069 / 1000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (1562069 / 1000000) = -Real.log (1000000 / 1562069) := by
    rw [show ((1562069 / 1000000) : ℝ) = ((1000000 / 1562069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (412846957 / 500000000) ≤ -Real.log (437931 / 1000000) ∧
    -Real.log (437931 / 1000000) ≤ (206423479 / 250000000) := by
  have h := checkLog_sound (w := (62069 / 937931)) (n := 12)
    (lo := (66273367 / 500000000)) (hi := (26509347 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 437931) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 437931) = 1/(437931 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-206423479 / 250000000) (-412846957 / 500000000) (Real.log (437931 / 1000000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1692003819 / 1000000000) ≤ -Real.log (62500000000 / 339396953621) ∧
    -Real.log (62500000000 / 339396953621) ≤ (846001911 / 500000000) := by
  have h := checkLog_sound (w := (89396953621 / 589396953621)) (n := 12)
    (lo := (305709459 / 1000000000)) (hi := (15285473 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339396953621 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(339396953621 / 250000000000) = 1/(62500000000 / 339396953621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1692003819 / 1000000000) (846001911 / 500000000) (Real.log (339396953621 / 62500000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (339396953621 / 62500000000) = -Real.log (62500000000 / 339396953621) := by
    rw [show ((339396953621 / 62500000000) : ℝ) = ((62500000000 / 339396953621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (340072387 / 200000000) ≤ -Real.log (250000000000 / 1368982243003) ∧
    -Real.log (250000000000 / 1368982243003) ≤ (850180969 / 500000000) := by
  have h := checkLog_sound (w := (368982243003 / 2368982243003)) (n := 12)
    (lo := (12562703 / 40000000)) (hi := (39258447 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1368982243003 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1368982243003 / 1000000000000) = 1/(250000000000 / 1368982243003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (340072387 / 200000000) (850180969 / 500000000) (Real.log (1368982243003 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (1368982243003 / 250000000000) = -Real.log (250000000000 / 1368982243003) := by
    rw [show ((1368982243003 / 250000000000) : ℝ) = ((250000000000 / 1368982243003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (253001597 / 200000000) ≤ -Real.log (500000000000 / 1771560516643) ∧
    -Real.log (500000000000 / 1771560516643) ≤ (1265007987 / 1000000000) := by
  have h := checkLog_sound (w := (771560516643 / 2771560516643)) (n := 12)
    (lo := (114372161 / 200000000)) (hi := (285930403 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771560516643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1771560516643 / 1000000000000) = 1/(500000000000 / 1771560516643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (253001597 / 200000000) (1265007987 / 1000000000) (Real.log (1771560516643 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1771560516643 / 500000000000) = -Real.log (500000000000 / 1771560516643) := by
    rw [show ((1771560516643 / 500000000000) : ℝ) = ((500000000000 / 1771560516643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (1271705139 / 1000000000) ≤ -Real.log (50000000000 / 178346474673) ∧
    -Real.log (50000000000 / 178346474673) ≤ (1271705141 / 1000000000) := by
  have h := checkLog_sound (w := (78346474673 / 278346474673)) (n := 12)
    (lo := (578557959 / 1000000000)) (hi := (14463949 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178346474673 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(178346474673 / 100000000000) = 1/(50000000000 / 178346474673) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (1271705139 / 1000000000) (1271705141 / 1000000000) (Real.log (178346474673 / 50000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (178346474673 / 50000000000) = -Real.log (50000000000 / 178346474673) := by
    rw [show ((178346474673 / 50000000000) : ℝ) = ((50000000000 / 178346474673) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0045

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapMiddle.Cell0046Logs =====
section
namespace GeneralCK.Certificates.DoubleCapMiddle.Cell0046
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

theorem reflection_log_1_neg : (4721757 / 12500000) ≤ -Real.log (512 / 747) ∧
    -Real.log (512 / 747) ≤ (377740561 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 1259)) (n := 12)
    (lo := (4721757 / 12500000)) (hi := (377740561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((747 / 512) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(747 / 512) = 1/(512 / 747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (4721757 / 12500000) (377740561 / 1000000000) (Real.log (747 / 512)) := by
  have h := reflection_log_1_neg
  have he : Real.log (747 / 512) = -Real.log (512 / 747) := by
    rw [show ((747 / 512) : ℝ) = ((512 / 747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (307153559 / 500000000) ≤ -Real.log (277 / 512) ∧
    -Real.log (277 / 512) ≤ (614307119 / 1000000000) := by
  have h := checkLog_sound (w := (235 / 789)) (n := 12)
    (lo := (307153559 / 500000000)) (hi := (614307119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((512 / 277) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(512 / 277) = 1/(277 / 512) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-614307119 / 1000000000) (-307153559 / 500000000) (Real.log (277 / 512)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (5889641 / 15625000) ≤ -Real.log (640 / 933) ∧
    -Real.log (640 / 933) ≤ (15077481 / 40000000) := by
  have h := checkLog_sound (w := (293 / 1573)) (n := 12)
    (lo := (5889641 / 15625000)) (hi := (15077481 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((933 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(933 / 640) = 1/(640 / 933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (5889641 / 15625000) (15077481 / 40000000) (Real.log (933 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (933 / 640) = -Real.log (640 / 933) := by
    rw [show ((933 / 640) : ℝ) = ((640 / 933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (153035849 / 250000000) ≤ -Real.log (347 / 640) ∧
    -Real.log (347 / 640) ≤ (612143397 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 987)) (n := 12)
    (lo := (153035849 / 250000000)) (hi := (612143397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 347) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 347) = 1/(347 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-612143397 / 1000000000) (-153035849 / 250000000) (Real.log (347 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (651266683 / 1000000000) ≤ -Real.log (256 / 491) ∧
    -Real.log (256 / 491) ≤ (162816671 / 250000000) := by
  have h := checkLog_sound (w := (235 / 747)) (n := 12)
    (lo := (651266683 / 1000000000)) (hi := (162816671 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((491 / 256) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(491 / 256) = 1/(256 / 491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (651266683 / 1000000000) (162816671 / 250000000) (Real.log (491 / 256)) := by
  have h := reflection_log_5_neg
  have he : Real.log (491 / 256) = -Real.log (256 / 491) := by
    rw [show ((491 / 256) : ℝ) = ((256 / 491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (500131001 / 200000000) ≤ -Real.log (21 / 256) ∧
    -Real.log (21 / 256) ≤ (2500655009 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(32 / 21) = 1/(21 / 256) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-2500655009 / 1000000000) (-500131001 / 200000000) (Real.log (21 / 256)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (32502197 / 50000000) ≤ -Real.log (320 / 613) ∧
    -Real.log (320 / 613) ≤ (650043941 / 1000000000) := by
  have h := checkLog_sound (w := (293 / 933)) (n := 12)
    (lo := (32502197 / 50000000)) (hi := (650043941 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((613 / 320) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(613 / 320) = 1/(320 / 613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (32502197 / 50000000) (650043941 / 1000000000) (Real.log (613 / 320)) := by
  have h := reflection_log_7_neg
  have he : Real.log (613 / 320) = -Real.log (320 / 613) := by
    rw [show ((613 / 320) : ℝ) = ((320 / 613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (77265129 / 31250000) ≤ -Real.log (27 / 320) ∧
    -Real.log (27 / 320) ≤ (618121033 / 250000000) := by
  have h := checkLog_sound (w := (13 / 67)) (n := 12)
    (lo := (98260647 / 250000000)) (hi := (393042589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40 / 27) : ℝ) 3 (by norm_num)
  have hq : (2 : ℝ)^3*(40 / 27) = 1/(27 / 320) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-618121033 / 250000000) (-77265129 / 31250000) (Real.log (27 / 320)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (65353933 / 125000000) ≤ -Real.log (1000000 / 1686797) ∧
    -Real.log (1000000 / 1686797) ≤ (104566293 / 200000000) := by
  have h := checkLog_sound (w := (686797 / 2686797)) (n := 12)
    (lo := (65353933 / 125000000)) (hi := (104566293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1686797 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1686797 / 1000000) = 1/(1000000 / 1686797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (65353933 / 125000000) (104566293 / 200000000) (Real.log (1686797 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1686797 / 1000000) = -Real.log (1000000 / 1686797) := by
    rw [show ((1686797 / 1000000) : ℝ) = ((1000000 / 1686797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (232180747 / 200000000) ≤ -Real.log (313203 / 1000000) ∧
    -Real.log (313203 / 1000000) ≤ (1160903737 / 1000000000) := by
  have h := checkLog_sound (w := (186797 / 813203)) (n := 12)
    (lo := (93551311 / 200000000)) (hi := (116939139 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 313203) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 313203) = 1/(313203 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1160903737 / 1000000000) (-232180747 / 200000000) (Real.log (313203 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (131030607 / 250000000) ≤ -Real.log (62500 / 105561) ∧
    -Real.log (62500 / 105561) ≤ (524122429 / 1000000000) := by
  have h := checkLog_sound (w := (43061 / 168061)) (n := 12)
    (lo := (131030607 / 250000000)) (hi := (524122429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((105561 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(105561 / 62500) = 1/(62500 / 105561) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (131030607 / 250000000) (524122429 / 1000000000) (Real.log (105561 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (105561 / 62500) = -Real.log (62500 / 105561) := by
    rw [show ((105561 / 62500) : ℝ) = ((62500 / 105561) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (583942599 / 500000000) ≤ -Real.log (19439 / 62500) ∧
    -Real.log (19439 / 62500) ≤ (2919713 / 2500000) := by
  have h := checkLog_sound (w := (11811 / 50689)) (n := 12)
    (lo := (237369009 / 500000000)) (hi := (474738019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 19439) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(31250 / 19439) = 1/(19439 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-2919713 / 2500000) (-583942599 / 500000000) (Real.log (19439 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (443079403 / 1000000000) ≤ -Real.log (125000 / 194687) ∧
    -Real.log (125000 / 194687) ≤ (110769851 / 250000000) := by
  have h := checkLog_sound (w := (69687 / 319687)) (n := 12)
    (lo := (443079403 / 1000000000)) (hi := (110769851 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((194687 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(194687 / 125000) = 1/(125000 / 194687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (443079403 / 1000000000) (110769851 / 250000000) (Real.log (194687 / 125000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (194687 / 125000) = -Real.log (125000 / 194687) := by
    rw [show ((194687 / 125000) : ℝ) = ((125000 / 194687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (407652887 / 500000000) ≤ -Real.log (55313 / 125000) ∧
    -Real.log (55313 / 125000) ≤ (50956611 / 62500000) := by
  have h := checkLog_sound (w := (7187 / 117813)) (n := 12)
    (lo := (61079297 / 500000000)) (hi := (24431719 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 55313) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 55313) = 1/(55313 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (-50956611 / 62500000) (-407652887 / 500000000) (Real.log (55313 / 125000)) := by
  have h := reflection_log_14_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15_neg : (22227079 / 50000000) ≤ -Real.log (40000 / 62391) ∧
    -Real.log (40000 / 62391) ≤ (444541581 / 1000000000) := by
  have h := checkLog_sound (w := (22391 / 102391)) (n := 12)
    (lo := (22227079 / 50000000)) (hi := (444541581 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62391 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62391 / 40000) = 1/(40000 / 62391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (22227079 / 50000000) (444541581 / 1000000000) (Real.log (62391 / 40000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (62391 / 40000) = -Real.log (40000 / 62391) := by
    rw [show ((62391 / 40000) : ℝ) = ((40000 / 62391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (410234659 / 500000000) ≤ -Real.log (17609 / 40000) ∧
    -Real.log (17609 / 40000) ≤ (20511733 / 25000000) := by
  have h := checkLog_sound (w := (2391 / 37609)) (n := 12)
    (lo := (63661069 / 500000000)) (hi := (127322139 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 17609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(20000 / 17609) = 1/(17609 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (-20511733 / 25000000) (-410234659 / 500000000) (Real.log (17609 / 40000)) := by
  have h := reflection_log_16_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_17_neg : (1683735199 / 1000000000) ≤ -Real.log (500000000000 / 2692817437891) ∧
    -Real.log (500000000000 / 2692817437891) ≤ (841867601 / 500000000) := by
  have h := checkLog_sound (w := (692817437891 / 4692817437891)) (n := 12)
    (lo := (297440839 / 1000000000)) (hi := (7436021 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2692817437891 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2692817437891 / 2000000000000) = 1/(500000000000 / 2692817437891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (1683735199 / 1000000000) (841867601 / 500000000) (Real.log (2692817437891 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (2692817437891 / 500000000000) = -Real.log (500000000000 / 2692817437891) := by
    rw [show ((2692817437891 / 500000000000) : ℝ) = ((500000000000 / 2692817437891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (846003813 / 500000000) ≤ -Real.log (500000000000 / 2715185966357) ∧
    -Real.log (500000000000 / 2715185966357) ≤ (1692007629 / 1000000000) := by
  have h := checkLog_sound (w := (715185966357 / 4715185966357)) (n := 12)
    (lo := (152856633 / 500000000)) (hi := (305713267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2715185966357 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2715185966357 / 2000000000000) = 1/(500000000000 / 2715185966357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (846003813 / 500000000) (1692007629 / 1000000000) (Real.log (2715185966357 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (2715185966357 / 500000000000) = -Real.log (500000000000 / 2715185966357) := by
    rw [show ((2715185966357 / 500000000000) : ℝ) = ((500000000000 / 2715185966357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1258385177 / 1000000000) ≤ -Real.log (500000000000 / 1759866577477) ∧
    -Real.log (500000000000 / 1759866577477) ≤ (1258385179 / 1000000000) := by
  have h := checkLog_sound (w := (759866577477 / 2759866577477)) (n := 12)
    (lo := (565237997 / 1000000000)) (hi := (282618999 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1759866577477 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1759866577477 / 1000000000000) = 1/(500000000000 / 1759866577477) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (1258385177 / 1000000000) (1258385179 / 1000000000) (Real.log (1759866577477 / 500000000000)) := by
  have h := reflection_log_19_neg
  have he : Real.log (1759866577477 / 500000000000) = -Real.log (500000000000 / 1759866577477) := by
    rw [show ((1759866577477 / 500000000000) : ℝ) = ((500000000000 / 1759866577477) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_20_neg : (632505449 / 500000000) ≤ -Real.log (500000000000 / 1771565676643) ∧
    -Real.log (500000000000 / 1771565676643) ≤ (12650109 / 10000000) := by
  have h := checkLog_sound (w := (771565676643 / 2771565676643)) (n := 12)
    (lo := (285931859 / 500000000)) (hi := (571863719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1771565676643 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1771565676643 / 1000000000000) = 1/(500000000000 / 1771565676643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (632505449 / 500000000) (12650109 / 10000000) (Real.log (1771565676643 / 500000000000)) := by
  have h := reflection_log_20_neg
  have he : Real.log (1771565676643 / 500000000000) = -Real.log (500000000000 / 1771565676643) := by
    rw [show ((1771565676643 / 500000000000) : ℝ) = ((500000000000 / 1771565676643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.DoubleCapMiddle.Cell0046

end


