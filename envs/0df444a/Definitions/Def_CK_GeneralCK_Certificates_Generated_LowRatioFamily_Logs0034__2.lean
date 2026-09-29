-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0034__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0034__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:57:18.983982+00:00
-- url     : https://prove2.me/theorems/cd4e9ae8-4476-48ef-8440-12214d713e6e
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0034 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0035)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0034 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0035)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0034 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0035)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0034 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0035) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0034 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0035).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0034 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2176_neg : (87080833 / 1000000000) ≤ -Real.log (916603 / 1000000) ∧
    -Real.log (916603 / 1000000) ≤ (43540417 / 500000000) := by
  have h := checkLog_sound (w := (83397 / 1916603)) (n := 12)
    (lo := (87080833 / 1000000000)) (hi := (43540417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916603) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916603) = 1/(916603 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2176 : Bounds (-43540417 / 500000000) (-87080833 / 1000000000) (Real.log (916603 / 1000000)) := by
  have h := reflection_log_2176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2177_neg : (3489679 / 500000000) ≤ -Real.log (993044940391 / 1000000000000) ∧
    -Real.log (993044940391 / 1000000000000) ≤ (6979359 / 1000000000) := by
  have h := checkLog_sound (w := (6955059609 / 1993044940391)) (n := 12)
    (lo := (3489679 / 500000000)) (hi := (6979359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993044940391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993044940391) = 1/(993044940391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2177 : Bounds (-6979359 / 1000000000) (-3489679 / 500000000) (Real.log (993044940391 / 1000000000000)) := by
  have h := reflection_log_2177_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2178_neg : (3471563 / 500000000) ≤ -Real.log (993080921239 / 1000000000000) ∧
    -Real.log (993080921239 / 1000000000000) ≤ (6943127 / 1000000000) := by
  have h := checkLog_sound (w := (6919078761 / 1993080921239)) (n := 12)
    (lo := (3471563 / 500000000)) (hi := (6943127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993080921239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993080921239) = 1/(993080921239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2178 : Bounds (-6943127 / 1000000000) (-3471563 / 500000000) (Real.log (993080921239 / 1000000000000)) := by
  have h := reflection_log_2178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2179_neg : (166747291 / 1000000000) ≤ -Real.log (250000000000 / 295363915887) ∧
    -Real.log (250000000000 / 295363915887) ≤ (41686823 / 250000000) := by
  have h := checkLog_sound (w := (45363915887 / 545363915887)) (n := 12)
    (lo := (166747291 / 1000000000)) (hi := (41686823 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295363915887 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295363915887 / 250000000000) = 1/(250000000000 / 295363915887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2179 : Bounds (166747291 / 1000000000) (41686823 / 250000000) (Real.log (295363915887 / 250000000000)) := by
  have h := reflection_log_2179_neg
  have he : Real.log (295363915887 / 250000000000) = -Real.log (250000000000 / 295363915887) := by
    rw [show ((295363915887 / 250000000000) : ℝ) = ((250000000000 / 295363915887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2180_neg : (167182309 / 1000000000) ≤ -Real.log (500000000000 / 590984864767) ∧
    -Real.log (500000000000 / 590984864767) ≤ (16718231 / 100000000) := by
  have h := checkLog_sound (w := (90984864767 / 1090984864767)) (n := 12)
    (lo := (167182309 / 1000000000)) (hi := (16718231 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590984864767 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590984864767 / 500000000000) = 1/(500000000000 / 590984864767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2180 : Bounds (167182309 / 1000000000) (16718231 / 100000000) (Real.log (590984864767 / 500000000000)) := by
  have h := reflection_log_2180_neg
  have he : Real.log (590984864767 / 500000000000) = -Real.log (500000000000 / 590984864767) := by
    rw [show ((590984864767 / 500000000000) : ℝ) = ((500000000000 / 590984864767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2181_neg : (167241997 / 500000000) ≤ -Real.log (500000000000 / 698609612849) ∧
    -Real.log (500000000000 / 698609612849) ≤ (66896799 / 200000000) := by
  have h := checkLog_sound (w := (198609612849 / 1198609612849)) (n := 12)
    (lo := (167241997 / 500000000)) (hi := (66896799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698609612849 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698609612849 / 500000000000) = 1/(500000000000 / 698609612849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2181 : Bounds (167241997 / 500000000) (66896799 / 200000000) (Real.log (698609612849 / 500000000000)) := by
  have h := reflection_log_2181_neg
  have he : Real.log (698609612849 / 500000000000) = -Real.log (500000000000 / 698609612849) := by
    rw [show ((698609612849 / 500000000000) : ℝ) = ((500000000000 / 698609612849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2182_neg : (334689643 / 1000000000) ≤ -Real.log (125000000000 / 174688324143) ∧
    -Real.log (125000000000 / 174688324143) ≤ (83672411 / 250000000) := by
  have h := checkLog_sound (w := (49688324143 / 299688324143)) (n := 12)
    (lo := (334689643 / 1000000000)) (hi := (83672411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((174688324143 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(174688324143 / 125000000000) = 1/(125000000000 / 174688324143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2182 : Bounds (334689643 / 1000000000) (83672411 / 250000000) (Real.log (174688324143 / 125000000000)) := by
  have h := reflection_log_2182_neg
  have he : Real.log (174688324143 / 125000000000) = -Real.log (125000000000 / 174688324143) := by
    rw [show ((174688324143 / 125000000000) : ℝ) = ((125000000000 / 174688324143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2183_neg : (3837333 / 25000000) ≤ -Real.log (10000 / 11659) ∧
    -Real.log (10000 / 11659) ≤ (153493321 / 1000000000) := by
  have h := checkLog_sound (w := (1659 / 21659)) (n := 12)
    (lo := (3837333 / 25000000)) (hi := (153493321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11659 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11659 / 10000) = 1/(10000 / 11659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2183 : Bounds (3837333 / 25000000) (153493321 / 1000000000) (Real.log (11659 / 10000)) := by
  have h := reflection_log_2183_neg
  have he : Real.log (11659 / 10000) = -Real.log (10000 / 11659) := by
    rw [show ((11659 / 10000) : ℝ) = ((10000 / 11659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2184_neg : (181401979 / 1000000000) ≤ -Real.log (8341 / 10000) ∧
    -Real.log (8341 / 10000) ≤ (9070099 / 50000000) := by
  have h := checkLog_sound (w := (1659 / 18341)) (n := 12)
    (lo := (181401979 / 1000000000)) (hi := (9070099 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8341) = 1/(8341 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2184 : Bounds (-9070099 / 50000000) (-181401979 / 1000000000) (Real.log (8341 / 10000)) := by
  have h := reflection_log_2184_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2185_neg : (82943 / 500000000) ≤ -Real.log (10000000 / 10001659) ∧
    -Real.log (10000000 / 10001659) ≤ (165887 / 1000000000) := by
  have h := checkLog_sound (w := (1659 / 20001659)) (n := 12)
    (lo := (82943 / 500000000)) (hi := (165887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001659 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001659 / 10000000) = 1/(10000000 / 10001659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2185 : Bounds (82943 / 500000000) (165887 / 1000000000) (Real.log (10001659 / 10000000)) := by
  have h := reflection_log_2185_neg
  have he : Real.log (10001659 / 10000000) = -Real.log (10000000 / 10001659) := by
    rw [show ((10001659 / 10000000) : ℝ) = ((10000000 / 10001659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2186_neg : (165913 / 1000000000) ≤ -Real.log (9998341 / 10000000) ∧
    -Real.log (9998341 / 10000000) ≤ (82957 / 500000000) := by
  have h := checkLog_sound (w := (1659 / 19998341)) (n := 12)
    (lo := (165913 / 1000000000)) (hi := (82957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998341) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998341) = 1/(9998341 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2186 : Bounds (-82957 / 500000000) (-165913 / 1000000000) (Real.log (9998341 / 10000000)) := by
  have h := reflection_log_2186_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2187_neg : (79948241 / 1000000000) ≤ -Real.log (1000000 / 1083231) ∧
    -Real.log (1000000 / 1083231) ≤ (39974121 / 500000000) := by
  have h := checkLog_sound (w := (83231 / 2083231)) (n := 12)
    (lo := (79948241 / 1000000000)) (hi := (39974121 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083231 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083231 / 1000000) = 1/(1000000 / 1083231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2187 : Bounds (79948241 / 1000000000) (39974121 / 500000000) (Real.log (1083231 / 1000000)) := by
  have h := reflection_log_2187_neg
  have he : Real.log (1083231 / 1000000) = -Real.log (1000000 / 1083231) := by
    rw [show ((1083231 / 1000000) : ℝ) = ((1000000 / 1083231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2188_neg : (43449873 / 500000000) ≤ -Real.log (916769 / 1000000) ∧
    -Real.log (916769 / 1000000) ≤ (86899747 / 1000000000) := by
  have h := checkLog_sound (w := (83231 / 1916769)) (n := 12)
    (lo := (43449873 / 500000000)) (hi := (86899747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916769) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916769) = 1/(916769 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2188 : Bounds (-86899747 / 1000000000) (-43449873 / 500000000) (Real.log (916769 / 1000000)) := by
  have h := reflection_log_2188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2189_neg : (20037137 / 250000000) ≤ -Real.log (125000 / 135431) ∧
    -Real.log (125000 / 135431) ≤ (80148549 / 1000000000) := by
  have h := checkLog_sound (w := (10431 / 260431)) (n := 12)
    (lo := (20037137 / 250000000)) (hi := (80148549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((135431 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(135431 / 125000) = 1/(125000 / 135431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2189 : Bounds (20037137 / 250000000) (80148549 / 1000000000) (Real.log (135431 / 125000)) := by
  have h := reflection_log_2189_neg
  have he : Real.log (135431 / 125000) = -Real.log (125000 / 135431) := by
    rw [show ((135431 / 125000) : ℝ) = ((125000 / 135431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2190_neg : (3485459 / 40000000) ≤ -Real.log (114569 / 125000) ∧
    -Real.log (114569 / 125000) ≤ (21784119 / 250000000) := by
  have h := checkLog_sound (w := (10431 / 239569)) (n := 12)
    (lo := (3485459 / 40000000)) (hi := (21784119 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 114569) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 114569) = 1/(114569 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2190 : Bounds (-21784119 / 250000000) (-3485459 / 40000000) (Real.log (114569 / 125000)) := by
  have h := reflection_log_2190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2191_neg : (6987927 / 1000000000) ≤ -Real.log (15516194239 / 15625000000) ∧
    -Real.log (15516194239 / 15625000000) ≤ (873491 / 125000000) := by
  have h := checkLog_sound (w := (108805761 / 31141194239)) (n := 12)
    (lo := (6987927 / 1000000000)) (hi := (873491 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15516194239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15516194239) = 1/(15516194239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2191 : Bounds (-873491 / 125000000) (-6987927 / 1000000000) (Real.log (15516194239 / 15625000000)) := by
  have h := reflection_log_2191_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2192_neg : (1390301 / 200000000) ≤ -Real.log (993072600639 / 1000000000000) ∧
    -Real.log (993072600639 / 1000000000000) ≤ (3475753 / 500000000) := by
  have h := checkLog_sound (w := (6927399361 / 1993072600639)) (n := 12)
    (lo := (1390301 / 200000000)) (hi := (3475753 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993072600639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993072600639) = 1/(993072600639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2192 : Bounds (-3475753 / 500000000) (-1390301 / 200000000) (Real.log (993072600639 / 1000000000000)) := by
  have h := reflection_log_2192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2193_neg : (41711997 / 250000000) ≤ -Real.log (500000000000 / 590787319379) ∧
    -Real.log (500000000000 / 590787319379) ≤ (166847989 / 1000000000) := by
  have h := checkLog_sound (w := (90787319379 / 1090787319379)) (n := 12)
    (lo := (41711997 / 250000000)) (hi := (166847989 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590787319379 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590787319379 / 500000000000) = 1/(500000000000 / 590787319379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2193 : Bounds (41711997 / 250000000) (166847989 / 1000000000) (Real.log (590787319379 / 500000000000)) := by
  have h := reflection_log_2193_neg
  have he : Real.log (590787319379 / 500000000000) = -Real.log (500000000000 / 590787319379) := by
    rw [show ((590787319379 / 500000000000) : ℝ) = ((500000000000 / 590787319379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2194_neg : (167285023 / 1000000000) ≤ -Real.log (62500000000 / 73880696349) ∧
    -Real.log (62500000000 / 73880696349) ≤ (5227657 / 31250000) := by
  have h := checkLog_sound (w := (11380696349 / 136380696349)) (n := 12)
    (lo := (167285023 / 1000000000)) (hi := (5227657 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73880696349 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73880696349 / 62500000000) = 1/(62500000000 / 73880696349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2194 : Bounds (167285023 / 1000000000) (5227657 / 31250000) (Real.log (73880696349 / 62500000000)) := by
  have h := reflection_log_2194_neg
  have he : Real.log (73880696349 / 62500000000) = -Real.log (62500000000 / 73880696349) := by
    rw [show ((73880696349 / 62500000000) : ℝ) = ((62500000000 / 73880696349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2195_neg : (334689643 / 1000000000) ≤ -Real.log (500000000000 / 698753296571) ∧
    -Real.log (500000000000 / 698753296571) ≤ (83672411 / 250000000) := by
  have h := checkLog_sound (w := (198753296571 / 1198753296571)) (n := 12)
    (lo := (334689643 / 1000000000)) (hi := (83672411 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698753296571 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698753296571 / 500000000000) = 1/(500000000000 / 698753296571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2195 : Bounds (334689643 / 1000000000) (83672411 / 250000000) (Real.log (698753296571 / 500000000000)) := by
  have h := reflection_log_2195_neg
  have he : Real.log (698753296571 / 500000000000) = -Real.log (500000000000 / 698753296571) := by
    rw [show ((698753296571 / 500000000000) : ℝ) = ((500000000000 / 698753296571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2196_neg : (3348953 / 10000000) ≤ -Real.log (500000000000 / 698897014747) ∧
    -Real.log (500000000000 / 698897014747) ≤ (334895301 / 1000000000) := by
  have h := checkLog_sound (w := (198897014747 / 1198897014747)) (n := 12)
    (lo := (3348953 / 10000000)) (hi := (334895301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((698897014747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(698897014747 / 500000000000) = 1/(500000000000 / 698897014747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2196 : Bounds (3348953 / 10000000) (334895301 / 1000000000) (Real.log (698897014747 / 500000000000)) := by
  have h := reflection_log_2196_neg
  have he : Real.log (698897014747 / 500000000000) = -Real.log (500000000000 / 698897014747) := by
    rw [show ((698897014747 / 500000000000) : ℝ) = ((500000000000 / 698897014747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2197_neg : (153579087 / 1000000000) ≤ -Real.log (500 / 583) ∧
    -Real.log (500 / 583) ≤ (9598693 / 62500000) := by
  have h := checkLog_sound (w := (83 / 1083)) (n := 12)
    (lo := (153579087 / 1000000000)) (hi := (9598693 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((583 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(583 / 500) = 1/(500 / 583) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2197 : Bounds (153579087 / 1000000000) (9598693 / 62500000) (Real.log (583 / 500)) := by
  have h := reflection_log_2197_neg
  have he : Real.log (583 / 500) = -Real.log (500 / 583) := by
    rw [show ((583 / 500) : ℝ) = ((500 / 583) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2198_neg : (45380469 / 250000000) ≤ -Real.log (417 / 500) ∧
    -Real.log (417 / 500) ≤ (181521877 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 917)) (n := 12)
    (lo := (45380469 / 250000000)) (hi := (181521877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 417) = 1/(417 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2198 : Bounds (-181521877 / 1000000000) (-45380469 / 250000000) (Real.log (417 / 500)) := by
  have h := reflection_log_2198_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2199_neg : (82993 / 500000000) ≤ -Real.log (500000 / 500083) ∧
    -Real.log (500000 / 500083) ≤ (165987 / 1000000000) := by
  have h := checkLog_sound (w := (83 / 1000083)) (n := 12)
    (lo := (82993 / 500000000)) (hi := (165987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500083 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500083 / 500000) = 1/(500000 / 500083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2199 : Bounds (82993 / 500000000) (165987 / 1000000000) (Real.log (500083 / 500000)) := by
  have h := reflection_log_2199_neg
  have he : Real.log (500083 / 500000) = -Real.log (500000 / 500083) := by
    rw [show ((500083 / 500000) : ℝ) = ((500000 / 500083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2200_neg : (166013 / 1000000000) ≤ -Real.log (499917 / 500000) ∧
    -Real.log (499917 / 500000) ≤ (83007 / 500000000) := by
  have h := checkLog_sound (w := (83 / 999917)) (n := 12)
    (lo := (166013 / 1000000000)) (hi := (83007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499917) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499917) = 1/(499917 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2200 : Bounds (-83007 / 500000000) (-166013 / 1000000000) (Real.log (499917 / 500000)) := by
  have h := reflection_log_2200_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2201_neg : (79995321 / 1000000000) ≤ -Real.log (500000 / 541641) ∧
    -Real.log (500000 / 541641) ≤ (39997661 / 500000000) := by
  have h := checkLog_sound (w := (41641 / 1041641)) (n := 12)
    (lo := (79995321 / 1000000000)) (hi := (39997661 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541641 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541641 / 500000) = 1/(500000 / 541641) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2201 : Bounds (79995321 / 1000000000) (39997661 / 500000000) (Real.log (541641 / 500000)) := by
  have h := reflection_log_2201_neg
  have he : Real.log (541641 / 500000) = -Real.log (500000 / 541641) := by
    rw [show ((541641 / 500000) : ℝ) = ((500000 / 541641) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2202_neg : (43477689 / 500000000) ≤ -Real.log (458359 / 500000) ∧
    -Real.log (458359 / 500000) ≤ (86955379 / 1000000000) := by
  have h := checkLog_sound (w := (41641 / 958359)) (n := 12)
    (lo := (43477689 / 500000000)) (hi := (86955379 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458359) = 1/(458359 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2202 : Bounds (-86955379 / 1000000000) (-43477689 / 500000000) (Real.log (458359 / 500000)) := by
  have h := reflection_log_2202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2203_neg : (80195619 / 1000000000) ≤ -Real.log (1000000 / 1083499) ∧
    -Real.log (1000000 / 1083499) ≤ (4009781 / 50000000) := by
  have h := checkLog_sound (w := (83499 / 2083499)) (n := 12)
    (lo := (80195619 / 1000000000)) (hi := (4009781 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083499 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083499 / 1000000) = 1/(1000000 / 1083499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2203 : Bounds (80195619 / 1000000000) (4009781 / 50000000) (Real.log (1083499 / 1000000)) := by
  have h := reflection_log_2203_neg
  have he : Real.log (1083499 / 1000000) = -Real.log (1000000 / 1083499) := by
    rw [show ((1083499 / 1000000) : ℝ) = ((1000000 / 1083499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2204_neg : (2179803 / 25000000) ≤ -Real.log (916501 / 1000000) ∧
    -Real.log (916501 / 1000000) ≤ (87192121 / 1000000000) := by
  have h := checkLog_sound (w := (83499 / 1916501)) (n := 12)
    (lo := (2179803 / 25000000)) (hi := (87192121 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916501) = 1/(916501 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2204 : Bounds (-87192121 / 1000000000) (-2179803 / 25000000) (Real.log (916501 / 1000000)) := by
  have h := reflection_log_2204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2205_neg : (6996501 / 1000000000) ≤ -Real.log (993027916999 / 1000000000000) ∧
    -Real.log (993027916999 / 1000000000000) ≤ (3498251 / 500000000) := by
  have h := checkLog_sound (w := (6972083001 / 1993027916999)) (n := 12)
    (lo := (6996501 / 1000000000)) (hi := (3498251 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993027916999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993027916999) = 1/(993027916999 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2205 : Bounds (-3498251 / 500000000) (-6996501 / 1000000000) (Real.log (993027916999 / 1000000000000)) := by
  have h := reflection_log_2205_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2206_neg : (870007 / 125000000) ≤ -Real.log (248266027119 / 250000000000) ∧
    -Real.log (248266027119 / 250000000000) ≤ (6960057 / 1000000000) := by
  have h := checkLog_sound (w := (1733972881 / 498266027119)) (n := 12)
    (lo := (870007 / 125000000)) (hi := (6960057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248266027119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248266027119) = 1/(248266027119 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2206 : Bounds (-6960057 / 1000000000) (-870007 / 125000000) (Real.log (248266027119 / 250000000000)) := by
  have h := reflection_log_2206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2207_neg : (1669507 / 10000000) ≤ -Real.log (25000000000 / 29542400171) ∧
    -Real.log (25000000000 / 29542400171) ≤ (166950701 / 1000000000) := by
  have h := checkLog_sound (w := (4542400171 / 54542400171)) (n := 12)
    (lo := (1669507 / 10000000)) (hi := (166950701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((29542400171 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(29542400171 / 25000000000) = 1/(25000000000 / 29542400171) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2207 : Bounds (1669507 / 10000000) (166950701 / 1000000000) (Real.log (29542400171 / 25000000000)) := by
  have h := reflection_log_2207_neg
  have he : Real.log (29542400171 / 25000000000) = -Real.log (25000000000 / 29542400171) := by
    rw [show ((29542400171 / 25000000000) : ℝ) = ((25000000000 / 29542400171) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2208_neg : (167387739 / 1000000000) ≤ -Real.log (125000000000 / 147776570893) ∧
    -Real.log (125000000000 / 147776570893) ≤ (8369387 / 50000000) := by
  have h := checkLog_sound (w := (22776570893 / 272776570893)) (n := 12)
    (lo := (167387739 / 1000000000)) (hi := (8369387 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147776570893 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147776570893 / 125000000000) = 1/(125000000000 / 147776570893) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2208 : Bounds (167387739 / 1000000000) (8369387 / 50000000) (Real.log (147776570893 / 125000000000)) := by
  have h := reflection_log_2208_neg
  have he : Real.log (147776570893 / 125000000000) = -Real.log (125000000000 / 147776570893) := by
    rw [show ((147776570893 / 125000000000) : ℝ) = ((125000000000 / 147776570893) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2209_neg : (3348953 / 10000000) ≤ -Real.log (250000000000 / 349448507373) ∧
    -Real.log (250000000000 / 349448507373) ≤ (334895301 / 1000000000) := by
  have h := checkLog_sound (w := (99448507373 / 599448507373)) (n := 12)
    (lo := (3348953 / 10000000)) (hi := (334895301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349448507373 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349448507373 / 250000000000) = 1/(250000000000 / 349448507373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2209 : Bounds (3348953 / 10000000) (334895301 / 1000000000) (Real.log (349448507373 / 250000000000)) := by
  have h := reflection_log_2209_neg
  have he : Real.log (349448507373 / 250000000000) = -Real.log (250000000000 / 349448507373) := by
    rw [show ((349448507373 / 250000000000) : ℝ) = ((250000000000 / 349448507373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2210_neg : (83775241 / 250000000) ≤ -Real.log (500000000000 / 699040767387) ∧
    -Real.log (500000000000 / 699040767387) ≤ (67020193 / 200000000) := by
  have h := checkLog_sound (w := (199040767387 / 1199040767387)) (n := 12)
    (lo := (83775241 / 250000000)) (hi := (67020193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699040767387 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699040767387 / 500000000000) = 1/(500000000000 / 699040767387) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2210 : Bounds (83775241 / 250000000) (67020193 / 200000000) (Real.log (699040767387 / 500000000000)) := by
  have h := reflection_log_2210_neg
  have he : Real.log (699040767387 / 500000000000) = -Real.log (500000000000 / 699040767387) := by
    rw [show ((699040767387 / 500000000000) : ℝ) = ((500000000000 / 699040767387) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2211_neg : (153664847 / 1000000000) ≤ -Real.log (10000 / 11661) ∧
    -Real.log (10000 / 11661) ≤ (9604053 / 62500000) := by
  have h := checkLog_sound (w := (1661 / 21661)) (n := 12)
    (lo := (153664847 / 1000000000)) (hi := (9604053 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11661 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11661 / 10000) = 1/(10000 / 11661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2211 : Bounds (153664847 / 1000000000) (9604053 / 62500000) (Real.log (11661 / 10000)) := by
  have h := reflection_log_2211_neg
  have he : Real.log (11661 / 10000) = -Real.log (10000 / 11661) := by
    rw [show ((11661 / 10000) : ℝ) = ((10000 / 11661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2212_neg : (181641787 / 1000000000) ≤ -Real.log (8339 / 10000) ∧
    -Real.log (8339 / 10000) ≤ (45410447 / 250000000) := by
  have h := checkLog_sound (w := (1661 / 18339)) (n := 12)
    (lo := (181641787 / 1000000000)) (hi := (45410447 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8339) = 1/(8339 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2212 : Bounds (-45410447 / 250000000) (-181641787 / 1000000000) (Real.log (8339 / 10000)) := by
  have h := reflection_log_2212_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2213_neg : (83043 / 500000000) ≤ -Real.log (10000000 / 10001661) ∧
    -Real.log (10000000 / 10001661) ≤ (166087 / 1000000000) := by
  have h := checkLog_sound (w := (1661 / 20001661)) (n := 12)
    (lo := (83043 / 500000000)) (hi := (166087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001661 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001661 / 10000000) = 1/(10000000 / 10001661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2213 : Bounds (83043 / 500000000) (166087 / 1000000000) (Real.log (10001661 / 10000000)) := by
  have h := reflection_log_2213_neg
  have he : Real.log (10001661 / 10000000) = -Real.log (10000000 / 10001661) := by
    rw [show ((10001661 / 10000000) : ℝ) = ((10000000 / 10001661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2214_neg : (166113 / 1000000000) ≤ -Real.log (9998339 / 10000000) ∧
    -Real.log (9998339 / 10000000) ≤ (83057 / 500000000) := by
  have h := checkLog_sound (w := (1661 / 19998339)) (n := 12)
    (lo := (166113 / 1000000000)) (hi := (83057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998339) = 1/(9998339 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2214 : Bounds (-83057 / 500000000) (-166113 / 1000000000) (Real.log (9998339 / 10000000)) := by
  have h := reflection_log_2214_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2215_neg : (80042399 / 1000000000) ≤ -Real.log (1000000 / 1083333) ∧
    -Real.log (1000000 / 1083333) ≤ (100053 / 1250000) := by
  have h := checkLog_sound (w := (83333 / 2083333)) (n := 12)
    (lo := (80042399 / 1000000000)) (hi := (100053 / 1250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083333 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083333 / 1000000) = 1/(1000000 / 1083333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2215 : Bounds (80042399 / 1000000000) (100053 / 1250000) (Real.log (1083333 / 1000000)) := by
  have h := reflection_log_2215_neg
  have he : Real.log (1083333 / 1000000) = -Real.log (1000000 / 1083333) := by
    rw [show ((1083333 / 1000000) : ℝ) = ((1000000 / 1083333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2216_neg : (87011013 / 1000000000) ≤ -Real.log (916667 / 1000000) ∧
    -Real.log (916667 / 1000000) ≤ (43505507 / 500000000) := by
  have h := checkLog_sound (w := (83333 / 1916667)) (n := 12)
    (lo := (87011013 / 1000000000)) (hi := (43505507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916667) = 1/(916667 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2216 : Bounds (-43505507 / 500000000) (-87011013 / 1000000000) (Real.log (916667 / 1000000)) := by
  have h := reflection_log_2216_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2217_neg : (80242687 / 1000000000) ≤ -Real.log (20000 / 21671) ∧
    -Real.log (20000 / 21671) ≤ (156724 / 1953125) := by
  have h := checkLog_sound (w := (1671 / 41671)) (n := 12)
    (lo := (80242687 / 1000000000)) (hi := (156724 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21671 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(21671 / 20000) = 1/(20000 / 21671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2217 : Bounds (80242687 / 1000000000) (156724 / 1953125) (Real.log (21671 / 20000)) := by
  have h := reflection_log_2217_neg
  have he : Real.log (21671 / 20000) = -Real.log (20000 / 21671) := by
    rw [show ((21671 / 20000) : ℝ) = ((20000 / 21671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2218_neg : (10905971 / 125000000) ≤ -Real.log (18329 / 20000) ∧
    -Real.log (18329 / 20000) ≤ (87247769 / 1000000000) := by
  have h := checkLog_sound (w := (1671 / 38329)) (n := 12)
    (lo := (10905971 / 125000000)) (hi := (87247769 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 18329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 18329) = 1/(18329 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2218 : Bounds (-87247769 / 1000000000) (-10905971 / 125000000) (Real.log (18329 / 20000)) := by
  have h := reflection_log_2218_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2219_neg : (175127 / 25000000) ≤ -Real.log (397207759 / 400000000) ∧
    -Real.log (397207759 / 400000000) ≤ (7005081 / 1000000000) := by
  have h := checkLog_sound (w := (2792241 / 797207759)) (n := 12)
    (lo := (175127 / 25000000)) (hi := (7005081 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 397207759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 397207759) = 1/(397207759 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2219 : Bounds (-7005081 / 1000000000) (-175127 / 25000000) (Real.log (397207759 / 400000000)) := by
  have h := reflection_log_2219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2220_neg : (6968613 / 1000000000) ≤ -Real.log (993055611111 / 1000000000000) ∧
    -Real.log (993055611111 / 1000000000000) ≤ (3484307 / 500000000) := by
  have h := checkLog_sound (w := (6944388889 / 1993055611111)) (n := 12)
    (lo := (6968613 / 1000000000)) (hi := (3484307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993055611111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993055611111) = 1/(993055611111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2220 : Bounds (-3484307 / 500000000) (-6968613 / 1000000000) (Real.log (993055611111 / 1000000000000)) := by
  have h := reflection_log_2220_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2221_neg : (167053413 / 1000000000) ≤ -Real.log (100000000000 / 118181738843) ∧
    -Real.log (100000000000 / 118181738843) ≤ (83526707 / 500000000) := by
  have h := checkLog_sound (w := (18181738843 / 218181738843)) (n := 12)
    (lo := (167053413 / 1000000000)) (hi := (83526707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118181738843 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118181738843 / 100000000000) = 1/(100000000000 / 118181738843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2221 : Bounds (167053413 / 1000000000) (83526707 / 500000000) (Real.log (118181738843 / 100000000000)) := by
  have h := reflection_log_2221_neg
  have he : Real.log (118181738843 / 100000000000) = -Real.log (100000000000 / 118181738843) := by
    rw [show ((118181738843 / 100000000000) : ℝ) = ((100000000000 / 118181738843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2222_neg : (20936307 / 125000000) ≤ -Real.log (50000000000 / 59116700311) ∧
    -Real.log (50000000000 / 59116700311) ≤ (167490457 / 1000000000) := by
  have h := checkLog_sound (w := (9116700311 / 109116700311)) (n := 12)
    (lo := (20936307 / 125000000)) (hi := (167490457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((59116700311 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(59116700311 / 50000000000) = 1/(50000000000 / 59116700311) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2222 : Bounds (20936307 / 125000000) (167490457 / 1000000000) (Real.log (59116700311 / 50000000000)) := by
  have h := reflection_log_2222_neg
  have he : Real.log (59116700311 / 50000000000) = -Real.log (50000000000 / 59116700311) := by
    rw [show ((59116700311 / 50000000000) : ℝ) = ((50000000000 / 59116700311) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2223_neg : (83775241 / 250000000) ≤ -Real.log (250000000000 / 349520383693) ∧
    -Real.log (250000000000 / 349520383693) ≤ (67020193 / 200000000) := by
  have h := checkLog_sound (w := (99520383693 / 599520383693)) (n := 12)
    (lo := (83775241 / 250000000)) (hi := (67020193 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349520383693 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349520383693 / 250000000000) = 1/(250000000000 / 349520383693) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2223 : Bounds (83775241 / 250000000) (67020193 / 200000000) (Real.log (349520383693 / 250000000000)) := by
  have h := reflection_log_2223_neg
  have he : Real.log (349520383693 / 250000000000) = -Real.log (250000000000 / 349520383693) := by
    rw [show ((349520383693 / 250000000000) : ℝ) = ((250000000000 / 349520383693) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2224_neg : (67061327 / 200000000) ≤ -Real.log (500000000000 / 699184554503) ∧
    -Real.log (500000000000 / 699184554503) ≤ (83826659 / 250000000) := by
  have h := checkLog_sound (w := (199184554503 / 1199184554503)) (n := 12)
    (lo := (67061327 / 200000000)) (hi := (83826659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699184554503 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699184554503 / 500000000000) = 1/(500000000000 / 699184554503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2224 : Bounds (67061327 / 200000000) (83826659 / 250000000) (Real.log (699184554503 / 500000000000)) := by
  have h := reflection_log_2224_neg
  have he : Real.log (699184554503 / 500000000000) = -Real.log (500000000000 / 699184554503) := by
    rw [show ((699184554503 / 500000000000) : ℝ) = ((500000000000 / 699184554503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2225_neg : (153750599 / 1000000000) ≤ -Real.log (5000 / 5831) ∧
    -Real.log (5000 / 5831) ≤ (768753 / 5000000) := by
  have h := checkLog_sound (w := (831 / 10831)) (n := 12)
    (lo := (153750599 / 1000000000)) (hi := (768753 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5831 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5831 / 5000) = 1/(5000 / 5831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2225 : Bounds (153750599 / 1000000000) (768753 / 5000000) (Real.log (5831 / 5000)) := by
  have h := reflection_log_2225_neg
  have he : Real.log (5831 / 5000) = -Real.log (5000 / 5831) := by
    rw [show ((5831 / 5000) : ℝ) = ((5000 / 5831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2226_neg : (181761713 / 1000000000) ≤ -Real.log (4169 / 5000) ∧
    -Real.log (4169 / 5000) ≤ (90880857 / 500000000) := by
  have h := checkLog_sound (w := (831 / 9169)) (n := 12)
    (lo := (181761713 / 1000000000)) (hi := (90880857 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4169) = 1/(4169 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2226 : Bounds (-90880857 / 500000000) (-181761713 / 1000000000) (Real.log (4169 / 5000)) := by
  have h := reflection_log_2226_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2227_neg : (83093 / 500000000) ≤ -Real.log (5000000 / 5000831) ∧
    -Real.log (5000000 / 5000831) ≤ (166187 / 1000000000) := by
  have h := checkLog_sound (w := (831 / 10000831)) (n := 12)
    (lo := (83093 / 500000000)) (hi := (166187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000831 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000831 / 5000000) = 1/(5000000 / 5000831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2227 : Bounds (83093 / 500000000) (166187 / 1000000000) (Real.log (5000831 / 5000000)) := by
  have h := reflection_log_2227_neg
  have he : Real.log (5000831 / 5000000) = -Real.log (5000000 / 5000831) := by
    rw [show ((5000831 / 5000000) : ℝ) = ((5000000 / 5000831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2228_neg : (166213 / 1000000000) ≤ -Real.log (4999169 / 5000000) ∧
    -Real.log (4999169 / 5000000) ≤ (83107 / 500000000) := by
  have h := checkLog_sound (w := (831 / 9999169)) (n := 12)
    (lo := (166213 / 1000000000)) (hi := (83107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999169) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999169) = 1/(4999169 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2228 : Bounds (-83107 / 500000000) (-166213 / 1000000000) (Real.log (4999169 / 5000000)) := by
  have h := reflection_log_2228_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2229_neg : (10011069 / 125000000) ≤ -Real.log (1000000 / 1083383) ∧
    -Real.log (1000000 / 1083383) ≤ (80088553 / 1000000000) := by
  have h := checkLog_sound (w := (83383 / 2083383)) (n := 12)
    (lo := (10011069 / 125000000)) (hi := (80088553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083383 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083383 / 1000000) = 1/(1000000 / 1083383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2229 : Bounds (10011069 / 125000000) (80088553 / 1000000000) (Real.log (1083383 / 1000000)) := by
  have h := reflection_log_2229_neg
  have he : Real.log (1083383 / 1000000) = -Real.log (1000000 / 1083383) := by
    rw [show ((1083383 / 1000000) : ℝ) = ((1000000 / 1083383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2230_neg : (2176639 / 25000000) ≤ -Real.log (916617 / 1000000) ∧
    -Real.log (916617 / 1000000) ≤ (87065561 / 1000000000) := by
  have h := checkLog_sound (w := (83383 / 1916617)) (n := 12)
    (lo := (2176639 / 25000000)) (hi := (87065561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916617) = 1/(916617 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2230 : Bounds (-87065561 / 1000000000) (-2176639 / 25000000) (Real.log (916617 / 1000000)) := by
  have h := reflection_log_2230_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2231_neg : (40144877 / 500000000) ≤ -Real.log (1000000 / 1083601) ∧
    -Real.log (1000000 / 1083601) ≤ (16057951 / 200000000) := by
  have h := checkLog_sound (w := (83601 / 2083601)) (n := 12)
    (lo := (40144877 / 500000000)) (hi := (16057951 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083601 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083601 / 1000000) = 1/(1000000 / 1083601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2231 : Bounds (40144877 / 500000000) (16057951 / 200000000) (Real.log (1083601 / 1000000)) := by
  have h := reflection_log_2231_neg
  have he : Real.log (1083601 / 1000000) = -Real.log (1000000 / 1083601) := by
    rw [show ((1083601 / 1000000) : ℝ) = ((1000000 / 1083601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2232_neg : (87303419 / 1000000000) ≤ -Real.log (916399 / 1000000) ∧
    -Real.log (916399 / 1000000) ≤ (4365171 / 50000000) := by
  have h := checkLog_sound (w := (83601 / 1916399)) (n := 12)
    (lo := (87303419 / 1000000000)) (hi := (4365171 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916399) = 1/(916399 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2232 : Bounds (-4365171 / 50000000) (-87303419 / 1000000000) (Real.log (916399 / 1000000)) := by
  have h := reflection_log_2232_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2233_neg : (1402733 / 200000000) ≤ -Real.log (993010872799 / 1000000000000) ∧
    -Real.log (993010872799 / 1000000000000) ≤ (3506833 / 500000000) := by
  have h := checkLog_sound (w := (6989127201 / 1993010872799)) (n := 12)
    (lo := (1402733 / 200000000)) (hi := (3506833 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993010872799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993010872799) = 1/(993010872799 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2233 : Bounds (-3506833 / 500000000) (-1402733 / 200000000) (Real.log (993010872799 / 1000000000000)) := by
  have h := reflection_log_2233_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2234_neg : (6977007 / 1000000000) ≤ -Real.log (993047275311 / 1000000000000) ∧
    -Real.log (993047275311 / 1000000000000) ≤ (436063 / 62500000) := by
  have h := checkLog_sound (w := (6952724689 / 1993047275311)) (n := 12)
    (lo := (6977007 / 1000000000)) (hi := (436063 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993047275311) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993047275311) = 1/(993047275311 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2234 : Bounds (-436063 / 62500000) (-6977007 / 1000000000) (Real.log (993047275311 / 1000000000000)) := by
  have h := reflection_log_2234_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2235_neg : (167154113 / 1000000000) ≤ -Real.log (500000000000 / 590968201549) ∧
    -Real.log (500000000000 / 590968201549) ≤ (83577057 / 500000000) := by
  have h := checkLog_sound (w := (90968201549 / 1090968201549)) (n := 12)
    (lo := (167154113 / 1000000000)) (hi := (83577057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590968201549 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590968201549 / 500000000000) = 1/(500000000000 / 590968201549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2235 : Bounds (167154113 / 1000000000) (83577057 / 500000000) (Real.log (590968201549 / 500000000000)) := by
  have h := reflection_log_2235_neg
  have he : Real.log (590968201549 / 500000000000) = -Real.log (500000000000 / 590968201549) := by
    rw [show ((590968201549 / 500000000000) : ℝ) = ((500000000000 / 590968201549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2236_neg : (167593173 / 1000000000) ≤ -Real.log (500000000000 / 591227729407) ∧
    -Real.log (500000000000 / 591227729407) ≤ (83796587 / 500000000) := by
  have h := checkLog_sound (w := (91227729407 / 1091227729407)) (n := 12)
    (lo := (167593173 / 1000000000)) (hi := (83796587 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591227729407 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591227729407 / 500000000000) = 1/(500000000000 / 591227729407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2236 : Bounds (167593173 / 1000000000) (83796587 / 500000000) (Real.log (591227729407 / 500000000000)) := by
  have h := reflection_log_2236_neg
  have he : Real.log (591227729407 / 500000000000) = -Real.log (500000000000 / 591227729407) := by
    rw [show ((591227729407 / 500000000000) : ℝ) = ((500000000000 / 591227729407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2237_neg : (67061327 / 200000000) ≤ -Real.log (250000000000 / 349592277251) ∧
    -Real.log (250000000000 / 349592277251) ≤ (83826659 / 250000000) := by
  have h := checkLog_sound (w := (99592277251 / 599592277251)) (n := 12)
    (lo := (67061327 / 200000000)) (hi := (83826659 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349592277251 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349592277251 / 250000000000) = 1/(250000000000 / 349592277251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2237 : Bounds (67061327 / 200000000) (83826659 / 250000000) (Real.log (349592277251 / 250000000000)) := by
  have h := reflection_log_2237_neg
  have he : Real.log (349592277251 / 250000000000) = -Real.log (250000000000 / 349592277251) := by
    rw [show ((349592277251 / 250000000000) : ℝ) = ((250000000000 / 349592277251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2238_neg : (335512313 / 1000000000) ≤ -Real.log (50000000000 / 69932837611) ∧
    -Real.log (50000000000 / 69932837611) ≤ (167756157 / 500000000) := by
  have h := checkLog_sound (w := (19932837611 / 119932837611)) (n := 12)
    (lo := (335512313 / 1000000000)) (hi := (167756157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69932837611 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69932837611 / 50000000000) = 1/(50000000000 / 69932837611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2238 : Bounds (335512313 / 1000000000) (167756157 / 500000000) (Real.log (69932837611 / 50000000000)) := by
  have h := reflection_log_2238_neg
  have he : Real.log (69932837611 / 50000000000) = -Real.log (50000000000 / 69932837611) := by
    rw [show ((69932837611 / 50000000000) : ℝ) = ((50000000000 / 69932837611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2239_neg : (19229543 / 125000000) ≤ -Real.log (10000 / 11663) ∧
    -Real.log (10000 / 11663) ≤ (30767269 / 200000000) := by
  have h := checkLog_sound (w := (1663 / 21663)) (n := 12)
    (lo := (19229543 / 125000000)) (hi := (30767269 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11663 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11663 / 10000) = 1/(10000 / 11663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2239 : Bounds (19229543 / 125000000) (30767269 / 200000000) (Real.log (11663 / 10000)) := by
  have h := reflection_log_2239_neg
  have he : Real.log (11663 / 10000) = -Real.log (10000 / 11663) := by
    rw [show ((11663 / 10000) : ℝ) = ((10000 / 11663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0035 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_2240_neg : (181881653 / 1000000000) ≤ -Real.log (8337 / 10000) ∧
    -Real.log (8337 / 10000) ≤ (90940827 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 18337)) (n := 12)
    (lo := (181881653 / 1000000000)) (hi := (90940827 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8337) = 1/(8337 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2240 : Bounds (-90940827 / 500000000) (-181881653 / 1000000000) (Real.log (8337 / 10000)) := by
  have h := reflection_log_2240_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2241_neg : (83143 / 500000000) ≤ -Real.log (10000000 / 10001663) ∧
    -Real.log (10000000 / 10001663) ≤ (166287 / 1000000000) := by
  have h := checkLog_sound (w := (1663 / 20001663)) (n := 12)
    (lo := (83143 / 500000000)) (hi := (166287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001663 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001663 / 10000000) = 1/(10000000 / 10001663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2241 : Bounds (83143 / 500000000) (166287 / 1000000000) (Real.log (10001663 / 10000000)) := by
  have h := reflection_log_2241_neg
  have he : Real.log (10001663 / 10000000) = -Real.log (10000000 / 10001663) := by
    rw [show ((10001663 / 10000000) : ℝ) = ((10000000 / 10001663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2242_neg : (166313 / 1000000000) ≤ -Real.log (9998337 / 10000000) ∧
    -Real.log (9998337 / 10000000) ≤ (83157 / 500000000) := by
  have h := checkLog_sound (w := (1663 / 19998337)) (n := 12)
    (lo := (166313 / 1000000000)) (hi := (83157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998337) = 1/(9998337 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2242 : Bounds (-83157 / 500000000) (-166313 / 1000000000) (Real.log (9998337 / 10000000)) := by
  have h := reflection_log_2242_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2243_neg : (40067813 / 500000000) ≤ -Real.log (500000 / 541717) ∧
    -Real.log (500000 / 541717) ≤ (80135627 / 1000000000) := by
  have h := checkLog_sound (w := (41717 / 1041717)) (n := 12)
    (lo := (40067813 / 500000000)) (hi := (80135627 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541717 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541717 / 500000) = 1/(500000 / 541717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2243 : Bounds (40067813 / 500000000) (80135627 / 1000000000) (Real.log (541717 / 500000)) := by
  have h := reflection_log_2243_neg
  have he : Real.log (541717 / 500000) = -Real.log (500000 / 541717) := by
    rw [show ((541717 / 500000) : ℝ) = ((500000 / 541717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2244_neg : (87121201 / 1000000000) ≤ -Real.log (458283 / 500000) ∧
    -Real.log (458283 / 500000) ≤ (43560601 / 500000000) := by
  have h := checkLog_sound (w := (41717 / 958283)) (n := 12)
    (lo := (87121201 / 1000000000)) (hi := (43560601 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458283) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458283) = 1/(458283 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2244 : Bounds (-43560601 / 500000000) (-87121201 / 1000000000) (Real.log (458283 / 500000)) := by
  have h := reflection_log_2244_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2245_neg : (16067179 / 200000000) ≤ -Real.log (1000000 / 1083651) ∧
    -Real.log (1000000 / 1083651) ≤ (10041987 / 125000000) := by
  have h := checkLog_sound (w := (83651 / 2083651)) (n := 12)
    (lo := (16067179 / 200000000)) (hi := (10041987 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083651 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083651 / 1000000) = 1/(1000000 / 1083651) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2245 : Bounds (16067179 / 200000000) (10041987 / 125000000) (Real.log (1083651 / 1000000)) := by
  have h := reflection_log_2245_neg
  have he : Real.log (1083651 / 1000000) = -Real.log (1000000 / 1083651) := by
    rw [show ((1083651 / 1000000) : ℝ) = ((1000000 / 1083651) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2246_neg : (43678991 / 500000000) ≤ -Real.log (916349 / 1000000) ∧
    -Real.log (916349 / 1000000) ≤ (87357983 / 1000000000) := by
  have h := checkLog_sound (w := (83651 / 1916349)) (n := 12)
    (lo := (43678991 / 500000000)) (hi := (87357983 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916349) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916349) = 1/(916349 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2246 : Bounds (-87357983 / 1000000000) (-43678991 / 500000000) (Real.log (916349 / 1000000)) := by
  have h := reflection_log_2246_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2247_neg : (7022087 / 1000000000) ≤ -Real.log (993002510199 / 1000000000000) ∧
    -Real.log (993002510199 / 1000000000000) ≤ (877761 / 125000000) := by
  have h := checkLog_sound (w := (6997489801 / 1993002510199)) (n := 12)
    (lo := (7022087 / 1000000000)) (hi := (877761 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993002510199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993002510199) = 1/(993002510199 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2247 : Bounds (-877761 / 125000000) (-7022087 / 1000000000) (Real.log (993002510199 / 1000000000000)) := by
  have h := reflection_log_2247_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2248_neg : (3492787 / 500000000) ≤ -Real.log (248259691911 / 250000000000) ∧
    -Real.log (248259691911 / 250000000000) ≤ (279423 / 40000000) := by
  have h := checkLog_sound (w := (1740308089 / 498259691911)) (n := 12)
    (lo := (3492787 / 500000000)) (hi := (279423 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248259691911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248259691911) = 1/(248259691911 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2248 : Bounds (-279423 / 40000000) (-3492787 / 500000000) (Real.log (248259691911 / 250000000000)) := by
  have h := reflection_log_2248_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2249_neg : (167256827 / 1000000000) ≤ -Real.log (500000000000 / 591028905719) ∧
    -Real.log (500000000000 / 591028905719) ≤ (41814207 / 250000000) := by
  have h := checkLog_sound (w := (91028905719 / 1091028905719)) (n := 12)
    (lo := (167256827 / 1000000000)) (hi := (41814207 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591028905719 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591028905719 / 500000000000) = 1/(500000000000 / 591028905719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2249 : Bounds (167256827 / 1000000000) (41814207 / 250000000) (Real.log (591028905719 / 500000000000)) := by
  have h := reflection_log_2249_neg
  have he : Real.log (591028905719 / 500000000000) = -Real.log (500000000000 / 591028905719) := by
    rw [show ((591028905719 / 500000000000) : ℝ) = ((500000000000 / 591028905719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2250_neg : (167693877 / 1000000000) ≤ -Real.log (500000000000 / 591287271553) ∧
    -Real.log (500000000000 / 591287271553) ≤ (83846939 / 500000000) := by
  have h := checkLog_sound (w := (91287271553 / 1091287271553)) (n := 12)
    (lo := (167693877 / 1000000000)) (hi := (83846939 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591287271553 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591287271553 / 500000000000) = 1/(500000000000 / 591287271553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2250 : Bounds (167693877 / 1000000000) (83846939 / 500000000) (Real.log (591287271553 / 500000000000)) := by
  have h := reflection_log_2250_neg
  have he : Real.log (591287271553 / 500000000000) = -Real.log (500000000000 / 591287271553) := by
    rw [show ((591287271553 / 500000000000) : ℝ) = ((500000000000 / 591287271553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2251_neg : (335512313 / 1000000000) ≤ -Real.log (500000000000 / 699328376109) ∧
    -Real.log (500000000000 / 699328376109) ≤ (167756157 / 500000000) := by
  have h := checkLog_sound (w := (199328376109 / 1199328376109)) (n := 12)
    (lo := (335512313 / 1000000000)) (hi := (167756157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699328376109 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699328376109 / 500000000000) = 1/(500000000000 / 699328376109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2251 : Bounds (335512313 / 1000000000) (167756157 / 500000000) (Real.log (699328376109 / 500000000000)) := by
  have h := reflection_log_2251_neg
  have he : Real.log (699328376109 / 500000000000) = -Real.log (500000000000 / 699328376109) := by
    rw [show ((699328376109 / 500000000000) : ℝ) = ((500000000000 / 699328376109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2252_neg : (167858999 / 500000000) ≤ -Real.log (250000000000 / 349736116109) ∧
    -Real.log (250000000000 / 349736116109) ≤ (335717999 / 1000000000) := by
  have h := checkLog_sound (w := (99736116109 / 599736116109)) (n := 12)
    (lo := (167858999 / 500000000)) (hi := (335717999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((349736116109 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(349736116109 / 250000000000) = 1/(250000000000 / 349736116109) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2252 : Bounds (167858999 / 500000000) (335717999 / 1000000000) (Real.log (349736116109 / 250000000000)) := by
  have h := reflection_log_2252_neg
  have he : Real.log (349736116109 / 250000000000) = -Real.log (250000000000 / 349736116109) := by
    rw [show ((349736116109 / 250000000000) : ℝ) = ((250000000000 / 349736116109) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2253_neg : (76961041 / 500000000) ≤ -Real.log (625 / 729) ∧
    -Real.log (625 / 729) ≤ (153922083 / 1000000000) := by
  have h := checkLog_sound (w := (52 / 677)) (n := 12)
    (lo := (76961041 / 500000000)) (hi := (153922083 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((729 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(729 / 625) = 1/(625 / 729) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2253 : Bounds (76961041 / 500000000) (153922083 / 1000000000) (Real.log (729 / 625)) := by
  have h := reflection_log_2253_neg
  have he : Real.log (729 / 625) = -Real.log (625 / 729) := by
    rw [show ((729 / 625) : ℝ) = ((625 / 729) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2254_neg : (182001607 / 1000000000) ≤ -Real.log (521 / 625) ∧
    -Real.log (521 / 625) ≤ (22750201 / 125000000) := by
  have h := checkLog_sound (w := (52 / 573)) (n := 12)
    (lo := (182001607 / 1000000000)) (hi := (22750201 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 521) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625 / 521) = 1/(521 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2254 : Bounds (-22750201 / 125000000) (-182001607 / 1000000000) (Real.log (521 / 625)) := by
  have h := reflection_log_2254_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2255_neg : (83193 / 500000000) ≤ -Real.log (78125 / 78138) ∧
    -Real.log (78125 / 78138) ≤ (166387 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 156263)) (n := 12)
    (lo := (83193 / 500000000)) (hi := (166387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78138 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78138 / 78125) = 1/(78125 / 78138) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2255 : Bounds (83193 / 500000000) (166387 / 1000000000) (Real.log (78138 / 78125)) := by
  have h := reflection_log_2255_neg
  have he : Real.log (78138 / 78125) = -Real.log (78125 / 78138) := by
    rw [show ((78138 / 78125) : ℝ) = ((78125 / 78138) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2256_neg : (166413 / 1000000000) ≤ -Real.log (78112 / 78125) ∧
    -Real.log (78112 / 78125) ≤ (83207 / 500000000) := by
  have h := checkLog_sound (w := (13 / 156237)) (n := 12)
    (lo := (166413 / 1000000000)) (hi := (83207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78112) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78112) = 1/(78112 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2256 : Bounds (-83207 / 500000000) (-166413 / 1000000000) (Real.log (78112 / 78125)) := by
  have h := reflection_log_2256_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2257_neg : (80182697 / 1000000000) ≤ -Real.log (200000 / 216697) ∧
    -Real.log (200000 / 216697) ≤ (40091349 / 500000000) := by
  have h := checkLog_sound (w := (16697 / 416697)) (n := 12)
    (lo := (80182697 / 1000000000)) (hi := (40091349 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216697 / 200000) = 1/(200000 / 216697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2257 : Bounds (80182697 / 1000000000) (40091349 / 500000000) (Real.log (216697 / 200000)) := by
  have h := reflection_log_2257_neg
  have he : Real.log (216697 / 200000) = -Real.log (200000 / 216697) := by
    rw [show ((216697 / 200000) : ℝ) = ((200000 / 216697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2258_neg : (17435369 / 200000000) ≤ -Real.log (183303 / 200000) ∧
    -Real.log (183303 / 200000) ≤ (43588423 / 500000000) := by
  have h := checkLog_sound (w := (16697 / 383303)) (n := 12)
    (lo := (17435369 / 200000000)) (hi := (43588423 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183303) = 1/(183303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2258 : Bounds (-43588423 / 500000000) (-17435369 / 200000000) (Real.log (183303 / 200000)) := by
  have h := reflection_log_2258_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2259_neg : (80382957 / 1000000000) ≤ -Real.log (500000 / 541851) ∧
    -Real.log (500000 / 541851) ≤ (40191479 / 500000000) := by
  have h := checkLog_sound (w := (41851 / 1041851)) (n := 12)
    (lo := (80382957 / 1000000000)) (hi := (40191479 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541851 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541851 / 500000) = 1/(500000 / 541851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2259 : Bounds (80382957 / 1000000000) (40191479 / 500000000) (Real.log (541851 / 500000)) := by
  have h := reflection_log_2259_neg
  have he : Real.log (541851 / 500000) = -Real.log (500000 / 541851) := by
    rw [show ((541851 / 500000) : ℝ) = ((500000 / 541851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2260_neg : (87413639 / 1000000000) ≤ -Real.log (458149 / 500000) ∧
    -Real.log (458149 / 500000) ≤ (2185341 / 25000000) := by
  have h := checkLog_sound (w := (41851 / 958149)) (n := 12)
    (lo := (87413639 / 1000000000)) (hi := (2185341 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458149) = 1/(458149 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2260 : Bounds (-2185341 / 25000000) (-87413639 / 1000000000) (Real.log (458149 / 500000)) := by
  have h := reflection_log_2260_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2261_neg : (3515341 / 500000000) ≤ -Real.log (248248493799 / 250000000000) ∧
    -Real.log (248248493799 / 250000000000) ≤ (7030683 / 1000000000) := by
  have h := checkLog_sound (w := (1751506201 / 498248493799)) (n := 12)
    (lo := (3515341 / 500000000)) (hi := (7030683 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248248493799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248248493799) = 1/(248248493799 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2261 : Bounds (-7030683 / 1000000000) (-3515341 / 500000000) (Real.log (248248493799 / 250000000000)) := by
  have h := reflection_log_2261_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2262_neg : (6994147 / 1000000000) ≤ -Real.log (39721210191 / 40000000000) ∧
    -Real.log (39721210191 / 40000000000) ≤ (1748537 / 250000000) := by
  have h := checkLog_sound (w := (278789809 / 79721210191)) (n := 12)
    (lo := (6994147 / 1000000000)) (hi := (1748537 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39721210191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39721210191) = 1/(39721210191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2262 : Bounds (-1748537 / 250000000) (-6994147 / 1000000000) (Real.log (39721210191 / 40000000000)) := by
  have h := reflection_log_2262_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2263_neg : (167359543 / 1000000000) ≤ -Real.log (100000000000 / 118217923329) ∧
    -Real.log (100000000000 / 118217923329) ≤ (20919943 / 125000000) := by
  have h := checkLog_sound (w := (18217923329 / 218217923329)) (n := 12)
    (lo := (167359543 / 1000000000)) (hi := (20919943 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118217923329 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118217923329 / 100000000000) = 1/(100000000000 / 118217923329) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2263 : Bounds (167359543 / 1000000000) (20919943 / 125000000) (Real.log (118217923329 / 100000000000)) := by
  have h := reflection_log_2263_neg
  have he : Real.log (118217923329 / 100000000000) = -Real.log (100000000000 / 118217923329) := by
    rw [show ((118217923329 / 100000000000) : ℝ) = ((100000000000 / 118217923329) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2264_neg : (167796597 / 1000000000) ≤ -Real.log (500000000000 / 591348011237) ∧
    -Real.log (500000000000 / 591348011237) ≤ (83898299 / 500000000) := by
  have h := checkLog_sound (w := (91348011237 / 1091348011237)) (n := 12)
    (lo := (167796597 / 1000000000)) (hi := (83898299 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591348011237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591348011237 / 500000000000) = 1/(500000000000 / 591348011237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2264 : Bounds (167796597 / 1000000000) (83898299 / 500000000) (Real.log (591348011237 / 500000000000)) := by
  have h := reflection_log_2264_neg
  have he : Real.log (591348011237 / 500000000000) = -Real.log (500000000000 / 591348011237) := by
    rw [show ((591348011237 / 500000000000) : ℝ) = ((500000000000 / 591348011237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2265_neg : (167858999 / 500000000) ≤ -Real.log (500000000000 / 699472232217) ∧
    -Real.log (500000000000 / 699472232217) ≤ (335717999 / 1000000000) := by
  have h := checkLog_sound (w := (199472232217 / 1199472232217)) (n := 12)
    (lo := (167858999 / 500000000)) (hi := (335717999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699472232217 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699472232217 / 500000000000) = 1/(500000000000 / 699472232217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2265 : Bounds (167858999 / 500000000) (335717999 / 1000000000) (Real.log (699472232217 / 500000000000)) := by
  have h := reflection_log_2265_neg
  have he : Real.log (699472232217 / 500000000000) = -Real.log (500000000000 / 699472232217) := by
    rw [show ((699472232217 / 500000000000) : ℝ) = ((500000000000 / 699472232217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2266_neg : (33592369 / 100000000) ≤ -Real.log (500000000000 / 699616122841) ∧
    -Real.log (500000000000 / 699616122841) ≤ (335923691 / 1000000000) := by
  have h := checkLog_sound (w := (199616122841 / 1199616122841)) (n := 12)
    (lo := (33592369 / 100000000)) (hi := (335923691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699616122841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699616122841 / 500000000000) = 1/(500000000000 / 699616122841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2266 : Bounds (33592369 / 100000000) (335923691 / 1000000000) (Real.log (699616122841 / 500000000000)) := by
  have h := reflection_log_2266_neg
  have he : Real.log (699616122841 / 500000000000) = -Real.log (500000000000 / 699616122841) := by
    rw [show ((699616122841 / 500000000000) : ℝ) = ((500000000000 / 699616122841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2267_neg : (38501953 / 250000000) ≤ -Real.log (2000 / 2333) ∧
    -Real.log (2000 / 2333) ≤ (154007813 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 4333)) (n := 12)
    (lo := (38501953 / 250000000)) (hi := (154007813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2333 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2333 / 2000) = 1/(2000 / 2333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2267 : Bounds (38501953 / 250000000) (154007813 / 1000000000) (Real.log (2333 / 2000)) := by
  have h := reflection_log_2267_neg
  have he : Real.log (2333 / 2000) = -Real.log (2000 / 2333) := by
    rw [show ((2333 / 2000) : ℝ) = ((2000 / 2333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2268_neg : (22765197 / 125000000) ≤ -Real.log (1667 / 2000) ∧
    -Real.log (1667 / 2000) ≤ (182121577 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 3667)) (n := 12)
    (lo := (22765197 / 125000000)) (hi := (182121577 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1667) = 1/(1667 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2268 : Bounds (-182121577 / 1000000000) (-22765197 / 125000000) (Real.log (1667 / 2000)) := by
  have h := reflection_log_2268_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2269_neg : (83243 / 500000000) ≤ -Real.log (2000000 / 2000333) ∧
    -Real.log (2000000 / 2000333) ≤ (166487 / 1000000000) := by
  have h := checkLog_sound (w := (333 / 4000333)) (n := 12)
    (lo := (83243 / 500000000)) (hi := (166487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000333 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000333 / 2000000) = 1/(2000000 / 2000333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2269 : Bounds (83243 / 500000000) (166487 / 1000000000) (Real.log (2000333 / 2000000)) := by
  have h := reflection_log_2269_neg
  have he : Real.log (2000333 / 2000000) = -Real.log (2000000 / 2000333) := by
    rw [show ((2000333 / 2000000) : ℝ) = ((2000000 / 2000333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2270_neg : (166513 / 1000000000) ≤ -Real.log (1999667 / 2000000) ∧
    -Real.log (1999667 / 2000000) ≤ (83257 / 500000000) := by
  have h := checkLog_sound (w := (333 / 3999667)) (n := 12)
    (lo := (166513 / 1000000000)) (hi := (83257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999667) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999667) = 1/(1999667 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2270 : Bounds (-83257 / 500000000) (-166513 / 1000000000) (Real.log (1999667 / 2000000)) := by
  have h := reflection_log_2270_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2271_neg : (80229767 / 1000000000) ≤ -Real.log (62500 / 67721) ∧
    -Real.log (62500 / 67721) ≤ (10028721 / 125000000) := by
  have h := checkLog_sound (w := (5221 / 130221)) (n := 12)
    (lo := (80229767 / 1000000000)) (hi := (10028721 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((67721 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(67721 / 62500) = 1/(62500 / 67721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2271 : Bounds (80229767 / 1000000000) (10028721 / 125000000) (Real.log (67721 / 62500)) := by
  have h := reflection_log_2271_neg
  have he : Real.log (67721 / 62500) = -Real.log (62500 / 67721) := by
    rw [show ((67721 / 62500) : ℝ) = ((62500 / 67721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2272_neg : (21808123 / 250000000) ≤ -Real.log (57279 / 62500) ∧
    -Real.log (57279 / 62500) ≤ (87232493 / 1000000000) := by
  have h := checkLog_sound (w := (5221 / 119779)) (n := 12)
    (lo := (21808123 / 250000000)) (hi := (87232493 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 57279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 57279) = 1/(57279 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2272 : Bounds (-87232493 / 1000000000) (-21808123 / 250000000) (Real.log (57279 / 62500)) := by
  have h := reflection_log_2272_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2273_neg : (80430017 / 1000000000) ≤ -Real.log (1000000 / 1083753) ∧
    -Real.log (1000000 / 1083753) ≤ (40215009 / 500000000) := by
  have h := checkLog_sound (w := (83753 / 2083753)) (n := 12)
    (lo := (80430017 / 1000000000)) (hi := (40215009 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083753 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083753 / 1000000) = 1/(1000000 / 1083753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2273 : Bounds (80430017 / 1000000000) (40215009 / 500000000) (Real.log (1083753 / 1000000)) := by
  have h := reflection_log_2273_neg
  have he : Real.log (1083753 / 1000000) = -Real.log (1000000 / 1083753) := by
    rw [show ((1083753 / 1000000) : ℝ) = ((1000000 / 1083753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2274_neg : (874693 / 10000000) ≤ -Real.log (916247 / 1000000) ∧
    -Real.log (916247 / 1000000) ≤ (87469301 / 1000000000) := by
  have h := checkLog_sound (w := (83753 / 1916247)) (n := 12)
    (lo := (874693 / 10000000)) (hi := (87469301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916247) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916247) = 1/(916247 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2274 : Bounds (-87469301 / 1000000000) (-874693 / 10000000) (Real.log (916247 / 1000000)) := by
  have h := reflection_log_2274_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2275_neg : (3519641 / 500000000) ≤ -Real.log (992985434991 / 1000000000000) ∧
    -Real.log (992985434991 / 1000000000000) ≤ (7039283 / 1000000000) := by
  have h := checkLog_sound (w := (7014565009 / 1992985434991)) (n := 12)
    (lo := (3519641 / 500000000)) (hi := (7039283 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992985434991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992985434991) = 1/(992985434991 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2275 : Bounds (-7039283 / 1000000000) (-3519641 / 500000000) (Real.log (992985434991 / 1000000000000)) := by
  have h := reflection_log_2275_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2276_neg : (280109 / 40000000) ≤ -Real.log (3878991159 / 3906250000) ∧
    -Real.log (3878991159 / 3906250000) ≤ (3501363 / 500000000) := by
  have h := checkLog_sound (w := (27258841 / 7785241159)) (n := 12)
    (lo := (280109 / 40000000)) (hi := (3501363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3878991159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3878991159) = 1/(3878991159 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2276 : Bounds (-3501363 / 500000000) (-280109 / 40000000) (Real.log (3878991159 / 3906250000)) := by
  have h := reflection_log_2276_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2277_neg : (167462259 / 1000000000) ≤ -Real.log (62500000000 / 73893791791) ∧
    -Real.log (62500000000 / 73893791791) ≤ (8373113 / 50000000) := by
  have h := checkLog_sound (w := (11393791791 / 136393791791)) (n := 12)
    (lo := (167462259 / 1000000000)) (hi := (8373113 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73893791791 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73893791791 / 62500000000) = 1/(62500000000 / 73893791791) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2277 : Bounds (167462259 / 1000000000) (8373113 / 50000000) (Real.log (73893791791 / 62500000000)) := by
  have h := reflection_log_2277_neg
  have he : Real.log (73893791791 / 62500000000) = -Real.log (62500000000 / 73893791791) := by
    rw [show ((73893791791 / 62500000000) : ℝ) = ((62500000000 / 73893791791) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2278_neg : (167899317 / 1000000000) ≤ -Real.log (500000000000 / 591408757683) ∧
    -Real.log (500000000000 / 591408757683) ≤ (83949659 / 500000000) := by
  have h := checkLog_sound (w := (91408757683 / 1091408757683)) (n := 12)
    (lo := (167899317 / 1000000000)) (hi := (83949659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591408757683 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591408757683 / 500000000000) = 1/(500000000000 / 591408757683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2278 : Bounds (167899317 / 1000000000) (83949659 / 500000000) (Real.log (591408757683 / 500000000000)) := by
  have h := reflection_log_2278_neg
  have he : Real.log (591408757683 / 500000000000) = -Real.log (500000000000 / 591408757683) := by
    rw [show ((591408757683 / 500000000000) : ℝ) = ((500000000000 / 591408757683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2279_neg : (33592369 / 100000000) ≤ -Real.log (12500000000 / 17490403071) ∧
    -Real.log (12500000000 / 17490403071) ≤ (335923691 / 1000000000) := by
  have h := checkLog_sound (w := (4990403071 / 29990403071)) (n := 12)
    (lo := (33592369 / 100000000)) (hi := (335923691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17490403071 / 12500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(17490403071 / 12500000000) = 1/(12500000000 / 17490403071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2279 : Bounds (33592369 / 100000000) (335923691 / 1000000000) (Real.log (17490403071 / 12500000000)) := by
  have h := reflection_log_2279_neg
  have he : Real.log (17490403071 / 12500000000) = -Real.log (12500000000 / 17490403071) := by
    rw [show ((17490403071 / 12500000000) : ℝ) = ((12500000000 / 17490403071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2280_neg : (336129389 / 1000000000) ≤ -Real.log (500000000000 / 699760047991) ∧
    -Real.log (500000000000 / 699760047991) ≤ (33612939 / 100000000) := by
  have h := checkLog_sound (w := (199760047991 / 1199760047991)) (n := 12)
    (lo := (336129389 / 1000000000)) (hi := (33612939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((699760047991 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(699760047991 / 500000000000) = 1/(500000000000 / 699760047991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2280 : Bounds (336129389 / 1000000000) (33612939 / 100000000) (Real.log (699760047991 / 500000000000)) := by
  have h := reflection_log_2280_neg
  have he : Real.log (699760047991 / 500000000000) = -Real.log (500000000000 / 699760047991) := by
    rw [show ((699760047991 / 500000000000) : ℝ) = ((500000000000 / 699760047991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2281_neg : (30818707 / 200000000) ≤ -Real.log (5000 / 5833) ∧
    -Real.log (5000 / 5833) ≤ (4815423 / 31250000) := by
  have h := checkLog_sound (w := (833 / 10833)) (n := 12)
    (lo := (30818707 / 200000000)) (hi := (4815423 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5833 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5833 / 5000) = 1/(5000 / 5833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2281 : Bounds (30818707 / 200000000) (4815423 / 31250000) (Real.log (5833 / 5000)) := by
  have h := reflection_log_2281_neg
  have he : Real.log (5833 / 5000) = -Real.log (5000 / 5833) := by
    rw [show ((5833 / 5000) : ℝ) = ((5000 / 5833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2282_neg : (182241559 / 1000000000) ≤ -Real.log (4167 / 5000) ∧
    -Real.log (4167 / 5000) ≤ (4556039 / 25000000) := by
  have h := checkLog_sound (w := (833 / 9167)) (n := 12)
    (lo := (182241559 / 1000000000)) (hi := (4556039 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4167) = 1/(4167 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2282 : Bounds (-4556039 / 25000000) (-182241559 / 1000000000) (Real.log (4167 / 5000)) := by
  have h := reflection_log_2282_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2283_neg : (83293 / 500000000) ≤ -Real.log (5000000 / 5000833) ∧
    -Real.log (5000000 / 5000833) ≤ (166587 / 1000000000) := by
  have h := checkLog_sound (w := (833 / 10000833)) (n := 12)
    (lo := (83293 / 500000000)) (hi := (166587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000833 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000833 / 5000000) = 1/(5000000 / 5000833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2283 : Bounds (83293 / 500000000) (166587 / 1000000000) (Real.log (5000833 / 5000000)) := by
  have h := reflection_log_2283_neg
  have he : Real.log (5000833 / 5000000) = -Real.log (5000000 / 5000833) := by
    rw [show ((5000833 / 5000000) : ℝ) = ((5000000 / 5000833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2284_neg : (166613 / 1000000000) ≤ -Real.log (4999167 / 5000000) ∧
    -Real.log (4999167 / 5000000) ≤ (83307 / 500000000) := by
  have h := checkLog_sound (w := (833 / 9999167)) (n := 12)
    (lo := (166613 / 1000000000)) (hi := (83307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999167) = 1/(4999167 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2284 : Bounds (-83307 / 500000000) (-166613 / 1000000000) (Real.log (4999167 / 5000000)) := by
  have h := reflection_log_2284_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2285_neg : (80275911 / 1000000000) ≤ -Real.log (500000 / 541793) ∧
    -Real.log (500000 / 541793) ≤ (10034489 / 125000000) := by
  have h := checkLog_sound (w := (41793 / 1041793)) (n := 12)
    (lo := (80275911 / 1000000000)) (hi := (10034489 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((541793 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(541793 / 500000) = 1/(500000 / 541793) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2285 : Bounds (80275911 / 1000000000) (10034489 / 125000000) (Real.log (541793 / 500000)) := by
  have h := reflection_log_2285_neg
  have he : Real.log (541793 / 500000) = -Real.log (500000 / 541793) := by
    rw [show ((541793 / 500000) : ℝ) = ((500000 / 541793) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2286_neg : (87287051 / 1000000000) ≤ -Real.log (458207 / 500000) ∧
    -Real.log (458207 / 500000) ≤ (21821763 / 250000000) := by
  have h := checkLog_sound (w := (41793 / 958207)) (n := 12)
    (lo := (87287051 / 1000000000)) (hi := (21821763 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 458207) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 458207) = 1/(458207 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2286 : Bounds (-21821763 / 250000000) (-87287051 / 1000000000) (Real.log (458207 / 500000)) := by
  have h := reflection_log_2286_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2287_neg : (40238537 / 500000000) ≤ -Real.log (250000 / 270951) ∧
    -Real.log (250000 / 270951) ≤ (3219083 / 40000000) := by
  have h := checkLog_sound (w := (20951 / 520951)) (n := 12)
    (lo := (40238537 / 500000000)) (hi := (3219083 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270951 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270951 / 250000) = 1/(250000 / 270951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2287 : Bounds (40238537 / 500000000) (3219083 / 40000000) (Real.log (270951 / 250000)) := by
  have h := reflection_log_2287_neg
  have he : Real.log (270951 / 250000) = -Real.log (250000 / 270951) := by
    rw [show ((270951 / 250000) : ℝ) = ((250000 / 270951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2288_neg : (87524963 / 1000000000) ≤ -Real.log (229049 / 250000) ∧
    -Real.log (229049 / 250000) ≤ (21881241 / 250000000) := by
  have h := checkLog_sound (w := (20951 / 479049)) (n := 12)
    (lo := (87524963 / 1000000000)) (hi := (21881241 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229049) = 1/(229049 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2288 : Bounds (-21881241 / 250000000) (-87524963 / 1000000000) (Real.log (229049 / 250000)) := by
  have h := reflection_log_2288_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2289_neg : (440493 / 62500000) ≤ -Real.log (62061055599 / 62500000000) ∧
    -Real.log (62061055599 / 62500000000) ≤ (7047889 / 1000000000) := by
  have h := checkLog_sound (w := (438944401 / 124561055599)) (n := 12)
    (lo := (440493 / 62500000)) (hi := (7047889 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62061055599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62061055599) = 1/(62061055599 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2289 : Bounds (-7047889 / 1000000000) (-440493 / 62500000) (Real.log (62061055599 / 62500000000)) := by
  have h := reflection_log_2289_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2290_neg : (350557 / 50000000) ≤ -Real.log (248253345151 / 250000000000) ∧
    -Real.log (248253345151 / 250000000000) ≤ (7011141 / 1000000000) := by
  have h := checkLog_sound (w := (1746654849 / 498253345151)) (n := 12)
    (lo := (350557 / 50000000)) (hi := (7011141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248253345151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248253345151) = 1/(248253345151 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2290 : Bounds (-7011141 / 1000000000) (-350557 / 50000000) (Real.log (248253345151 / 250000000000)) := by
  have h := reflection_log_2290_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2291_neg : (83781481 / 500000000) ≤ -Real.log (500000000000 / 591209868029) ∧
    -Real.log (500000000000 / 591209868029) ≤ (167562963 / 1000000000) := by
  have h := checkLog_sound (w := (91209868029 / 1091209868029)) (n := 12)
    (lo := (83781481 / 500000000)) (hi := (167562963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591209868029 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591209868029 / 500000000000) = 1/(500000000000 / 591209868029) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2291 : Bounds (83781481 / 500000000) (167562963 / 1000000000) (Real.log (591209868029 / 500000000000)) := by
  have h := reflection_log_2291_neg
  have he : Real.log (591209868029 / 500000000000) = -Real.log (500000000000 / 591209868029) := by
    rw [show ((591209868029 / 500000000000) : ℝ) = ((500000000000 / 591209868029) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2292_neg : (84001019 / 500000000) ≤ -Real.log (500000000000 / 591469510891) ∧
    -Real.log (500000000000 / 591469510891) ≤ (168002039 / 1000000000) := by
  have h := checkLog_sound (w := (91469510891 / 1091469510891)) (n := 12)
    (lo := (84001019 / 500000000)) (hi := (168002039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591469510891 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591469510891 / 500000000000) = 1/(500000000000 / 591469510891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2292 : Bounds (84001019 / 500000000) (168002039 / 1000000000) (Real.log (591469510891 / 500000000000)) := by
  have h := reflection_log_2292_neg
  have he : Real.log (591469510891 / 500000000000) = -Real.log (500000000000 / 591469510891) := by
    rw [show ((591469510891 / 500000000000) : ℝ) = ((500000000000 / 591469510891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2293_neg : (336129389 / 1000000000) ≤ -Real.log (50000000000 / 69976004799) ∧
    -Real.log (50000000000 / 69976004799) ≤ (33612939 / 100000000) := by
  have h := checkLog_sound (w := (19976004799 / 119976004799)) (n := 12)
    (lo := (336129389 / 1000000000)) (hi := (33612939 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((69976004799 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(69976004799 / 50000000000) = 1/(50000000000 / 69976004799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2293 : Bounds (336129389 / 1000000000) (33612939 / 100000000) (Real.log (69976004799 / 50000000000)) := by
  have h := reflection_log_2293_neg
  have he : Real.log (69976004799 / 50000000000) = -Real.log (50000000000 / 69976004799) := by
    rw [show ((69976004799 / 50000000000) : ℝ) = ((50000000000 / 69976004799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2294_neg : (67267019 / 200000000) ≤ -Real.log (195312500 / 273400003) ∧
    -Real.log (195312500 / 273400003) ≤ (42041887 / 125000000) := by
  have h := checkLog_sound (w := (78087503 / 468712503)) (n := 12)
    (lo := (67267019 / 200000000)) (hi := (42041887 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((273400003 / 195312500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(273400003 / 195312500) = 1/(195312500 / 273400003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2294 : Bounds (67267019 / 200000000) (42041887 / 125000000) (Real.log (273400003 / 195312500)) := by
  have h := reflection_log_2294_neg
  have he : Real.log (273400003 / 195312500) = -Real.log (195312500 / 273400003) := by
    rw [show ((273400003 / 195312500) : ℝ) = ((195312500 / 273400003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2295_neg : (616717 / 4000000) ≤ -Real.log (10000 / 11667) ∧
    -Real.log (10000 / 11667) ≤ (154179251 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 21667)) (n := 12)
    (lo := (616717 / 4000000)) (hi := (154179251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11667 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11667 / 10000) = 1/(10000 / 11667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2295 : Bounds (616717 / 4000000) (154179251 / 1000000000) (Real.log (11667 / 10000)) := by
  have h := reflection_log_2295_neg
  have he : Real.log (11667 / 10000) = -Real.log (10000 / 11667) := by
    rw [show ((11667 / 10000) : ℝ) = ((10000 / 11667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2296_neg : (182361557 / 1000000000) ≤ -Real.log (8333 / 10000) ∧
    -Real.log (8333 / 10000) ≤ (91180779 / 500000000) := by
  have h := checkLog_sound (w := (1667 / 18333)) (n := 12)
    (lo := (182361557 / 1000000000)) (hi := (91180779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8333) = 1/(8333 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2296 : Bounds (-91180779 / 500000000) (-182361557 / 1000000000) (Real.log (8333 / 10000)) := by
  have h := reflection_log_2296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2297_neg : (83343 / 500000000) ≤ -Real.log (10000000 / 10001667) ∧
    -Real.log (10000000 / 10001667) ≤ (166687 / 1000000000) := by
  have h := checkLog_sound (w := (1667 / 20001667)) (n := 12)
    (lo := (83343 / 500000000)) (hi := (166687 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001667 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001667 / 10000000) = 1/(10000000 / 10001667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2297 : Bounds (83343 / 500000000) (166687 / 1000000000) (Real.log (10001667 / 10000000)) := by
  have h := reflection_log_2297_neg
  have he : Real.log (10001667 / 10000000) = -Real.log (10000000 / 10001667) := by
    rw [show ((10001667 / 10000000) : ℝ) = ((10000000 / 10001667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2298_neg : (166713 / 1000000000) ≤ -Real.log (9998333 / 10000000) ∧
    -Real.log (9998333 / 10000000) ≤ (83357 / 500000000) := by
  have h := checkLog_sound (w := (1667 / 19998333)) (n := 12)
    (lo := (166713 / 1000000000)) (hi := (83357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998333) = 1/(9998333 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2298 : Bounds (-83357 / 500000000) (-166713 / 1000000000) (Real.log (9998333 / 10000000)) := by
  have h := reflection_log_2298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2299_neg : (2510093 / 31250000) ≤ -Real.log (1000000 / 1083637) ∧
    -Real.log (1000000 / 1083637) ≤ (80322977 / 1000000000) := by
  have h := checkLog_sound (w := (83637 / 2083637)) (n := 12)
    (lo := (2510093 / 31250000)) (hi := (80322977 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1083637 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1083637 / 1000000) = 1/(1000000 / 1083637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2299 : Bounds (2510093 / 31250000) (80322977 / 1000000000) (Real.log (1083637 / 1000000)) := by
  have h := reflection_log_2299_neg
  have he : Real.log (1083637 / 1000000) = -Real.log (1000000 / 1083637) := by
    rw [show ((1083637 / 1000000) : ℝ) = ((1000000 / 1083637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2300_neg : (5458919 / 62500000) ≤ -Real.log (916363 / 1000000) ∧
    -Real.log (916363 / 1000000) ≤ (17468541 / 200000000) := by
  have h := checkLog_sound (w := (83637 / 1916363)) (n := 12)
    (lo := (5458919 / 62500000)) (hi := (17468541 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 916363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 916363) = 1/(916363 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2300 : Bounds (-17468541 / 200000000) (-5458919 / 62500000) (Real.log (916363 / 1000000)) := by
  have h := reflection_log_2300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2301_neg : (8052413 / 100000000) ≤ -Real.log (200000 / 216771) ∧
    -Real.log (200000 / 216771) ≤ (80524131 / 1000000000) := by
  have h := checkLog_sound (w := (16771 / 416771)) (n := 12)
    (lo := (8052413 / 100000000)) (hi := (80524131 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216771 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216771 / 200000) = 1/(200000 / 216771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2301 : Bounds (8052413 / 100000000) (80524131 / 1000000000) (Real.log (216771 / 200000)) := by
  have h := reflection_log_2301_neg
  have he : Real.log (216771 / 200000) = -Real.log (200000 / 216771) := by
    rw [show ((216771 / 200000) : ℝ) = ((200000 / 216771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2302_neg : (87580629 / 1000000000) ≤ -Real.log (183229 / 200000) ∧
    -Real.log (183229 / 200000) ≤ (8758063 / 100000000) := by
  have h := checkLog_sound (w := (16771 / 383229)) (n := 12)
    (lo := (87580629 / 1000000000)) (hi := (8758063 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183229) = 1/(183229 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2302 : Bounds (-8758063 / 100000000) (-87580629 / 1000000000) (Real.log (183229 / 200000)) := by
  have h := reflection_log_2302_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_2303_neg : (7056499 / 1000000000) ≤ -Real.log (39718733559 / 40000000000) ∧
    -Real.log (39718733559 / 40000000000) ≤ (14113 / 2000000) := by
  have h := checkLog_sound (w := (281266441 / 79718733559)) (n := 12)
    (lo := (7056499 / 1000000000)) (hi := (14113 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39718733559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39718733559) = 1/(39718733559 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2303 : Bounds (-14113 / 2000000) (-7056499 / 1000000000) (Real.log (39718733559 / 40000000000)) := by
  have h := reflection_log_2303_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


