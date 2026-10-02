-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell162Logs__7
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell162Logs__7
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:41:04.766425+00:00
-- url     : https://prove2.me/theorems/cce20816-17d3-40f3-b133-925a3f1e7bdf
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell163…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell163Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell164Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell165Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell166Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell167Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell168Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell163Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell164Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell165Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell166Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell167Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell168Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell162Logs (+6 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell163Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell164Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell165Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell166Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell167Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell168Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell162Logs (+6 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell163Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell164Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell165Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell166Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell167Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell168Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell162Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell162
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (296771497 / 1000000000) ≤ -Real.log (5120 / 6889) ∧
    -Real.log (5120 / 6889) ≤ (148385749 / 500000000) := by
  have h := checkLog_sound (w := (1769 / 12009)) (n := 12)
    (lo := (296771497 / 1000000000)) (hi := (148385749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6889 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6889 / 5120) = 1/(5120 / 6889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (296771497 / 1000000000) (148385749 / 500000000) (Real.log (6889 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6889 / 5120) = -Real.log (5120 / 6889) := by
    rw [show ((6889 / 5120) : ℝ) = ((5120 / 6889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (42389563 / 100000000) ≤ -Real.log (3351 / 5120) ∧
    -Real.log (3351 / 5120) ≤ (423895631 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 8471)) (n := 12)
    (lo := (42389563 / 100000000)) (hi := (423895631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3351) = 1/(3351 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-423895631 / 1000000000) (-42389563 / 100000000) (Real.log (3351 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11853437 / 40000000) ≤ -Real.log (2560 / 3443) ∧
    -Real.log (2560 / 3443) ≤ (148167963 / 500000000) := by
  have h := checkLog_sound (w := (883 / 6003)) (n := 12)
    (lo := (11853437 / 40000000)) (hi := (148167963 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3443 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3443 / 2560) = 1/(2560 / 3443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11853437 / 40000000) (148167963 / 500000000) (Real.log (3443 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3443 / 2560) = -Real.log (2560 / 3443) := by
    rw [show ((3443 / 2560) : ℝ) = ((2560 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (16920031 / 40000000) ≤ -Real.log (1677 / 2560) ∧
    -Real.log (1677 / 2560) ≤ (52875097 / 125000000) := by
  have h := checkLog_sound (w := (883 / 4237)) (n := 12)
    (lo := (16920031 / 40000000)) (hi := (52875097 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1677) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1677) = 1/(1677 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-52875097 / 125000000) (-16920031 / 40000000) (Real.log (1677 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (219271263 / 1000000000) ≤ -Real.log (1000000 / 1245169) ∧
    -Real.log (1000000 / 1245169) ≤ (6852227 / 31250000) := by
  have h := checkLog_sound (w := (245169 / 2245169)) (n := 12)
    (lo := (219271263 / 1000000000)) (hi := (6852227 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245169 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245169 / 1000000) = 1/(1000000 / 1245169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (219271263 / 1000000000) (6852227 / 31250000) (Real.log (1245169 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1245169 / 1000000) = -Real.log (1000000 / 1245169) := by
    rw [show ((1245169 / 1000000) : ℝ) = ((1000000 / 1245169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (56252279 / 200000000) ≤ -Real.log (754831 / 1000000) ∧
    -Real.log (754831 / 1000000) ≤ (70315349 / 250000000) := by
  have h := checkLog_sound (w := (245169 / 1754831)) (n := 12)
    (lo := (56252279 / 200000000)) (hi := (70315349 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754831) = 1/(754831 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70315349 / 250000000) (-56252279 / 200000000) (Real.log (754831 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54902529 / 250000000) ≤ -Real.log (1000000 / 1245591) ∧
    -Real.log (1000000 / 1245591) ≤ (219610117 / 1000000000) := by
  have h := checkLog_sound (w := (245591 / 2245591)) (n := 12)
    (lo := (54902529 / 250000000)) (hi := (219610117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1245591 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1245591 / 1000000) = 1/(1000000 / 1245591) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54902529 / 250000000) (219610117 / 1000000000) (Real.log (1245591 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1245591 / 1000000) = -Real.log (1000000 / 1245591) := by
    rw [show ((1245591 / 1000000) : ℝ) = ((1000000 / 1245591) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (281820617 / 1000000000) ≤ -Real.log (754409 / 1000000) ∧
    -Real.log (754409 / 1000000) ≤ (140910309 / 500000000) := by
  have h := checkLog_sound (w := (245591 / 1754409)) (n := 12)
    (lo := (281820617 / 1000000000)) (hi := (140910309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 754409) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 754409) = 1/(754409 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-140910309 / 500000000) (-281820617 / 1000000000) (Real.log (754409 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (81185259 / 500000000) ≤ -Real.log (125000 / 147037) ∧
    -Real.log (125000 / 147037) ≤ (162370519 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 272037)) (n := 12)
    (lo := (81185259 / 500000000)) (hi := (162370519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147037 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147037 / 125000) = 1/(125000 / 147037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (81185259 / 500000000) (162370519 / 1000000000) (Real.log (147037 / 125000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (147037 / 125000) = -Real.log (125000 / 147037) := by
    rw [show ((147037 / 125000) : ℝ) = ((125000 / 147037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (48486009 / 250000000) ≤ -Real.log (102963 / 125000) ∧
    -Real.log (102963 / 125000) ≤ (193944037 / 1000000000) := by
  have h := checkLog_sound (w := (22037 / 227963)) (n := 12)
    (lo := (48486009 / 250000000)) (hi := (193944037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102963) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102963) = 1/(102963 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-193944037 / 1000000000) (-48486009 / 250000000) (Real.log (102963 / 125000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (81318711 / 500000000) ≤ -Real.log (100000 / 117661) ∧
    -Real.log (100000 / 117661) ≤ (162637423 / 1000000000) := by
  have h := checkLog_sound (w := (17661 / 217661)) (n := 12)
    (lo := (81318711 / 500000000)) (hi := (162637423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117661 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117661 / 100000) = 1/(100000 / 117661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (81318711 / 500000000) (162637423 / 1000000000) (Real.log (117661 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117661 / 100000) = -Real.log (100000 / 117661) := by
    rw [show ((117661 / 100000) : ℝ) = ((100000 / 117661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (97162657 / 500000000) ≤ -Real.log (82339 / 100000) ∧
    -Real.log (82339 / 100000) ≤ (38865063 / 200000000) := by
  have h := checkLog_sound (w := (17661 / 182339)) (n := 12)
    (lo := (97162657 / 500000000)) (hi := (38865063 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82339) = 1/(82339 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38865063 / 200000000) (-97162657 / 500000000) (Real.log (82339 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (7193367 / 10000000) ≤ -Real.log (500000000000 / 1026535480023) ∧
    -Real.log (500000000000 / 1026535480023) ≤ (359668351 / 500000000) := by
  have h := checkLog_sound (w := (26535480023 / 2026535480023)) (n := 12)
    (lo := (327369 / 12500000)) (hi := (26189521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1026535480023 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1026535480023 / 1000000000000) = 1/(500000000000 / 1026535480023) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (7193367 / 10000000) (359668351 / 500000000) (Real.log (1026535480023 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1026535480023 / 500000000000) = -Real.log (500000000000 / 1026535480023) := by
    rw [show ((1026535480023 / 500000000000) : ℝ) = ((500000000000 / 1026535480023) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (720667127 / 1000000000) ≤ -Real.log (500000000000 / 1027902118771) ∧
    -Real.log (500000000000 / 1027902118771) ≤ (720667129 / 1000000000) := by
  have h := checkLog_sound (w := (27902118771 / 2027902118771)) (n := 12)
    (lo := (27519947 / 1000000000)) (hi := (6879987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1027902118771 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1027902118771 / 1000000000000) = 1/(500000000000 / 1027902118771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (720667127 / 1000000000) (720667129 / 1000000000) (Real.log (1027902118771 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1027902118771 / 500000000000) = -Real.log (500000000000 / 1027902118771) := by
    rw [show ((1027902118771 / 500000000000) : ℝ) = ((500000000000 / 1027902118771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (500532659 / 1000000000) ≤ -Real.log (500000000000 / 824799855861) ∧
    -Real.log (500000000000 / 824799855861) ≤ (25026633 / 50000000) := by
  have h := checkLog_sound (w := (324799855861 / 1324799855861)) (n := 12)
    (lo := (500532659 / 1000000000)) (hi := (25026633 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824799855861 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824799855861 / 500000000000) = 1/(500000000000 / 824799855861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (500532659 / 1000000000) (25026633 / 50000000) (Real.log (824799855861 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (824799855861 / 500000000000) = -Real.log (500000000000 / 824799855861) := by
    rw [show ((824799855861 / 500000000000) : ℝ) = ((500000000000 / 824799855861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (501430733 / 1000000000) ≤ -Real.log (500000000000 / 825540920111) ∧
    -Real.log (500000000000 / 825540920111) ≤ (250715367 / 500000000) := by
  have h := checkLog_sound (w := (325540920111 / 1325540920111)) (n := 12)
    (lo := (501430733 / 1000000000)) (hi := (250715367 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((825540920111 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(825540920111 / 500000000000) = 1/(500000000000 / 825540920111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (501430733 / 1000000000) (250715367 / 500000000) (Real.log (825540920111 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (825540920111 / 500000000000) = -Real.log (500000000000 / 825540920111) := by
    rw [show ((825540920111 / 500000000000) : ℝ) = ((500000000000 / 825540920111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (71262911 / 200000000) ≤ -Real.log (500000000000 / 714028340277) ∧
    -Real.log (500000000000 / 714028340277) ≤ (89078639 / 250000000) := by
  have h := checkLog_sound (w := (214028340277 / 1214028340277)) (n := 12)
    (lo := (71262911 / 200000000)) (hi := (89078639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714028340277 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714028340277 / 500000000000) = 1/(500000000000 / 714028340277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (71262911 / 200000000) (89078639 / 250000000) (Real.log (714028340277 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714028340277 / 500000000000) = -Real.log (500000000000 / 714028340277) := by
    rw [show ((714028340277 / 500000000000) : ℝ) = ((500000000000 / 714028340277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (22310171 / 62500000) ≤ -Real.log (100000000000 / 142898262063) ∧
    -Real.log (100000000000 / 142898262063) ≤ (356962737 / 1000000000) := by
  have h := checkLog_sound (w := (42898262063 / 242898262063)) (n := 12)
    (lo := (22310171 / 62500000)) (hi := (356962737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142898262063 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142898262063 / 100000000000) = 1/(100000000000 / 142898262063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (22310171 / 62500000) (356962737 / 1000000000) (Real.log (142898262063 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142898262063 / 100000000000) = -Real.log (100000000000 / 142898262063) := by
    rw [show ((142898262063 / 100000000000) : ℝ) = ((100000000000 / 142898262063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7921973 / 250000000) ≤ -Real.log (9688089079 / 10000000000) ∧
    -Real.log (9688089079 / 10000000000) ≤ (31687893 / 1000000000) := by
  have h := checkLog_sound (w := (311910921 / 19688089079)) (n := 12)
    (lo := (7921973 / 250000000)) (hi := (31687893 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9688089079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9688089079) = 1/(9688089079 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31687893 / 1000000000) (-7921973 / 250000000) (Real.log (9688089079 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15786759 / 500000000) ≤ -Real.log (15139370631 / 15625000000) ∧
    -Real.log (15139370631 / 15625000000) ≤ (31573519 / 1000000000) := by
  have h := checkLog_sound (w := (485629369 / 30764370631)) (n := 12)
    (lo := (15786759 / 500000000)) (hi := (31573519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15139370631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15139370631) = 1/(15139370631 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31573519 / 1000000000) (-15786759 / 500000000) (Real.log (15139370631 / 15625000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell162

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell163Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell163
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (297206879 / 1000000000) ≤ -Real.log (1280 / 1723) ∧
    -Real.log (1280 / 1723) ≤ (1857543 / 6250000) := by
  have h := checkLog_sound (w := (443 / 3003)) (n := 12)
    (lo := (297206879 / 1000000000)) (hi := (1857543 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723 / 1280) = 1/(1280 / 1723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (297206879 / 1000000000) (1857543 / 6250000) (Real.log (1723 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1723 / 1280) = -Real.log (1280 / 1723) := by
    rw [show ((1723 / 1280) : ℝ) = ((1280 / 1723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (212395643 / 500000000) ≤ -Real.log (837 / 1280) ∧
    -Real.log (837 / 1280) ≤ (424791287 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2117)) (n := 12)
    (lo := (212395643 / 500000000)) (hi := (424791287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 837) = 1/(837 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-424791287 / 1000000000) (-212395643 / 500000000) (Real.log (837 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (296771497 / 1000000000) ≤ -Real.log (5120 / 6889) ∧
    -Real.log (5120 / 6889) ≤ (148385749 / 500000000) := by
  have h := checkLog_sound (w := (1769 / 12009)) (n := 12)
    (lo := (296771497 / 1000000000)) (hi := (148385749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6889 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6889 / 5120) = 1/(5120 / 6889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (296771497 / 1000000000) (148385749 / 500000000) (Real.log (6889 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6889 / 5120) = -Real.log (5120 / 6889) := by
    rw [show ((6889 / 5120) : ℝ) = ((5120 / 6889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (42389563 / 100000000) ≤ -Real.log (3351 / 5120) ∧
    -Real.log (3351 / 5120) ≤ (423895631 / 1000000000) := by
  have h := checkLog_sound (w := (1769 / 8471)) (n := 12)
    (lo := (42389563 / 100000000)) (hi := (423895631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3351) = 1/(3351 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-423895631 / 1000000000) (-42389563 / 100000000) (Real.log (3351 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (219609313 / 1000000000) ≤ -Real.log (100000 / 124559) ∧
    -Real.log (100000 / 124559) ≤ (109804657 / 500000000) := by
  have h := checkLog_sound (w := (24559 / 224559)) (n := 12)
    (lo := (219609313 / 1000000000)) (hi := (109804657 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124559 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124559 / 100000) = 1/(100000 / 124559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (219609313 / 1000000000) (109804657 / 500000000) (Real.log (124559 / 100000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (124559 / 100000) = -Real.log (100000 / 124559) := by
    rw [show ((124559 / 100000) : ℝ) = ((100000 / 124559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (70454823 / 250000000) ≤ -Real.log (75441 / 100000) ∧
    -Real.log (75441 / 100000) ≤ (281819293 / 1000000000) := by
  have h := checkLog_sound (w := (24559 / 175441)) (n := 12)
    (lo := (70454823 / 250000000)) (hi := (281819293 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75441) = 1/(75441 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-281819293 / 1000000000) (-70454823 / 250000000) (Real.log (75441 / 100000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (219948051 / 1000000000) ≤ -Real.log (250000 / 311503) ∧
    -Real.log (250000 / 311503) ≤ (54987013 / 250000000) := by
  have h := checkLog_sound (w := (61503 / 561503)) (n := 12)
    (lo := (219948051 / 1000000000)) (hi := (54987013 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311503 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311503 / 250000) = 1/(250000 / 311503) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (219948051 / 1000000000) (54987013 / 250000000) (Real.log (311503 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (311503 / 250000) = -Real.log (250000 / 311503) := by
    rw [show ((311503 / 250000) : ℝ) = ((250000 / 311503) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141189413 / 500000000) ≤ -Real.log (188497 / 250000) ∧
    -Real.log (188497 / 250000) ≤ (282378827 / 1000000000) := by
  have h := checkLog_sound (w := (61503 / 438497)) (n := 12)
    (lo := (141189413 / 500000000)) (hi := (282378827 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188497) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188497) = 1/(188497 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282378827 / 1000000000) (-141189413 / 500000000) (Real.log (188497 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40659143 / 250000000) ≤ -Real.log (1000000 / 1176609) ∧
    -Real.log (1000000 / 1176609) ≤ (162636573 / 1000000000) := by
  have h := checkLog_sound (w := (176609 / 2176609)) (n := 12)
    (lo := (40659143 / 250000000)) (hi := (162636573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176609 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176609 / 1000000) = 1/(1000000 / 1176609) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40659143 / 250000000) (162636573 / 1000000000) (Real.log (1176609 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1176609 / 1000000) = -Real.log (1000000 / 1176609) := by
    rw [show ((1176609 / 1000000) : ℝ) = ((1000000 / 1176609) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194324099 / 1000000000) ≤ -Real.log (823391 / 1000000) ∧
    -Real.log (823391 / 1000000) ≤ (1943241 / 10000000) := by
  have h := checkLog_sound (w := (176609 / 1823391)) (n := 12)
    (lo := (194324099 / 1000000000)) (hi := (1943241 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823391) = 1/(823391 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-1943241 / 10000000) (-194324099 / 1000000000) (Real.log (823391 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32580681 / 200000000) ≤ -Real.log (1000000 / 1176923) ∧
    -Real.log (1000000 / 1176923) ≤ (81451703 / 500000000) := by
  have h := checkLog_sound (w := (176923 / 2176923)) (n := 12)
    (lo := (32580681 / 200000000)) (hi := (81451703 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176923 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176923 / 1000000) = 1/(1000000 / 1176923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32580681 / 200000000) (81451703 / 500000000) (Real.log (1176923 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1176923 / 1000000) = -Real.log (1000000 / 1176923) := by
    rw [show ((1176923 / 1000000) : ℝ) = ((1000000 / 1176923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (97352761 / 500000000) ≤ -Real.log (823077 / 1000000) ∧
    -Real.log (823077 / 1000000) ≤ (194705523 / 1000000000) := by
  have h := checkLog_sound (w := (176923 / 1823077)) (n := 12)
    (lo := (97352761 / 500000000)) (hi := (194705523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823077) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823077) = 1/(823077 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-194705523 / 1000000000) (-97352761 / 500000000) (Real.log (823077 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (720667127 / 1000000000) ≤ -Real.log (50000000000 / 102790211877) ∧
    -Real.log (50000000000 / 102790211877) ≤ (720667129 / 1000000000) := by
  have h := checkLog_sound (w := (2790211877 / 202790211877)) (n := 12)
    (lo := (27519947 / 1000000000)) (hi := (6879987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102790211877 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102790211877 / 100000000000) = 1/(50000000000 / 102790211877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (720667127 / 1000000000) (720667129 / 1000000000) (Real.log (102790211877 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102790211877 / 50000000000) = -Real.log (50000000000 / 102790211877) := by
    rw [show ((102790211877 / 50000000000) : ℝ) = ((50000000000 / 102790211877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (144399633 / 200000000) ≤ -Real.log (500000000000 / 1029271206691) ∧
    -Real.log (500000000000 / 1029271206691) ≤ (721998167 / 1000000000) := by
  have h := checkLog_sound (w := (29271206691 / 2029271206691)) (n := 12)
    (lo := (5770197 / 200000000)) (hi := (14425493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1029271206691 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1029271206691 / 1000000000000) = 1/(500000000000 / 1029271206691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (144399633 / 200000000) (721998167 / 1000000000) (Real.log (1029271206691 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1029271206691 / 500000000000) = -Real.log (500000000000 / 1029271206691) := by
    rw [show ((1029271206691 / 500000000000) : ℝ) = ((500000000000 / 1029271206691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (100285721 / 200000000) ≤ -Real.log (250000000000 / 412769581527) ∧
    -Real.log (250000000000 / 412769581527) ≤ (250714303 / 500000000) := by
  have h := checkLog_sound (w := (162769581527 / 662769581527)) (n := 12)
    (lo := (100285721 / 200000000)) (hi := (250714303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412769581527 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412769581527 / 250000000000) = 1/(250000000000 / 412769581527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (100285721 / 200000000) (250714303 / 500000000) (Real.log (412769581527 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (412769581527 / 250000000000) = -Real.log (250000000000 / 412769581527) := by
    rw [show ((412769581527 / 250000000000) : ℝ) = ((250000000000 / 412769581527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (502326877 / 1000000000) ≤ -Real.log (500000000000 / 826281054871) ∧
    -Real.log (500000000000 / 826281054871) ≤ (251163439 / 500000000) := by
  have h := checkLog_sound (w := (326281054871 / 1326281054871)) (n := 12)
    (lo := (502326877 / 1000000000)) (hi := (251163439 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826281054871 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826281054871 / 500000000000) = 1/(500000000000 / 826281054871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (502326877 / 1000000000) (251163439 / 500000000) (Real.log (826281054871 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (826281054871 / 500000000000) = -Real.log (500000000000 / 826281054871) := by
    rw [show ((826281054871 / 500000000000) : ℝ) = ((500000000000 / 826281054871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (11155021 / 31250000) ≤ -Real.log (500000000000 / 714489835327) ∧
    -Real.log (500000000000 / 714489835327) ≤ (356960673 / 1000000000) := by
  have h := checkLog_sound (w := (214489835327 / 1214489835327)) (n := 12)
    (lo := (11155021 / 31250000)) (hi := (356960673 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714489835327 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714489835327 / 500000000000) = 1/(500000000000 / 714489835327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (11155021 / 31250000) (356960673 / 1000000000) (Real.log (714489835327 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714489835327 / 500000000000) = -Real.log (500000000000 / 714489835327) := by
    rw [show ((714489835327 / 500000000000) : ℝ) = ((500000000000 / 714489835327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (11175279 / 31250000) ≤ -Real.log (250000000000 / 357476578741) ∧
    -Real.log (250000000000 / 357476578741) ≤ (357608929 / 1000000000) := by
  have h := checkLog_sound (w := (107476578741 / 607476578741)) (n := 12)
    (lo := (11175279 / 31250000)) (hi := (357608929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357476578741 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357476578741 / 250000000000) = 1/(250000000000 / 357476578741) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (11175279 / 31250000) (357608929 / 1000000000) (Real.log (357476578741 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (357476578741 / 250000000000) = -Real.log (250000000000 / 357476578741) := by
    rw [show ((357476578741 / 250000000000) : ℝ) = ((250000000000 / 357476578741) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7950529 / 250000000) ≤ -Real.log (968698252071 / 1000000000000) ∧
    -Real.log (968698252071 / 1000000000000) ≤ (31802117 / 1000000000) := by
  have h := checkLog_sound (w := (31301747929 / 1968698252071)) (n := 12)
    (lo := (7950529 / 250000000)) (hi := (31802117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968698252071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968698252071) = 1/(968698252071 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31802117 / 1000000000) (-7950529 / 250000000) (Real.log (968698252071 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31687527 / 1000000000) ≤ -Real.log (968809261119 / 1000000000000) ∧
    -Real.log (968809261119 / 1000000000000) ≤ (3960941 / 125000000) := by
  have h := checkLog_sound (w := (31190738881 / 1968809261119)) (n := 12)
    (lo := (31687527 / 1000000000)) (hi := (3960941 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968809261119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968809261119) = 1/(968809261119 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3960941 / 125000000) (-31687527 / 1000000000) (Real.log (968809261119 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell163

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell164Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell164
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (37205259 / 125000000) ≤ -Real.log (1024 / 1379) ∧
    -Real.log (1024 / 1379) ≤ (297642073 / 1000000000) := by
  have h := checkLog_sound (w := (355 / 2403)) (n := 12)
    (lo := (37205259 / 125000000)) (hi := (297642073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1024) = 1/(1024 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (37205259 / 125000000) (297642073 / 1000000000) (Real.log (1379 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1379 / 1024) = -Real.log (1024 / 1379) := by
    rw [show ((1379 / 1024) : ℝ) = ((1024 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (85137549 / 200000000) ≤ -Real.log (669 / 1024) ∧
    -Real.log (669 / 1024) ≤ (212843873 / 500000000) := by
  have h := checkLog_sound (w := (355 / 1693)) (n := 12)
    (lo := (85137549 / 200000000)) (hi := (212843873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 669) = 1/(669 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-212843873 / 500000000) (-85137549 / 200000000) (Real.log (669 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (297206879 / 1000000000) ≤ -Real.log (1280 / 1723) ∧
    -Real.log (1280 / 1723) ≤ (1857543 / 6250000) := by
  have h := checkLog_sound (w := (443 / 3003)) (n := 12)
    (lo := (297206879 / 1000000000)) (hi := (1857543 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1723 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1723 / 1280) = 1/(1280 / 1723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (297206879 / 1000000000) (1857543 / 6250000) (Real.log (1723 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1723 / 1280) = -Real.log (1280 / 1723) := by
    rw [show ((1723 / 1280) : ℝ) = ((1280 / 1723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (212395643 / 500000000) ≤ -Real.log (837 / 1280) ∧
    -Real.log (837 / 1280) ≤ (424791287 / 1000000000) := by
  have h := checkLog_sound (w := (443 / 2117)) (n := 12)
    (lo := (212395643 / 500000000)) (hi := (424791287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 837) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 837) = 1/(837 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-424791287 / 1000000000) (-212395643 / 500000000) (Real.log (837 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (13746703 / 62500000) ≤ -Real.log (1000000 / 1246011) ∧
    -Real.log (1000000 / 1246011) ≤ (219947249 / 1000000000) := by
  have h := checkLog_sound (w := (246011 / 2246011)) (n := 12)
    (lo := (13746703 / 62500000)) (hi := (219947249 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246011 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246011 / 1000000) = 1/(1000000 / 1246011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (13746703 / 62500000) (219947249 / 1000000000) (Real.log (1246011 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1246011 / 1000000) = -Real.log (1000000 / 1246011) := by
    rw [show ((1246011 / 1000000) : ℝ) = ((1000000 / 1246011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282377499 / 1000000000) ≤ -Real.log (753989 / 1000000) ∧
    -Real.log (753989 / 1000000) ≤ (112951 / 400000) := by
  have h := checkLog_sound (w := (246011 / 1753989)) (n := 12)
    (lo := (282377499 / 1000000000)) (hi := (112951 / 400000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753989) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753989) = 1/(753989 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-112951 / 400000) (-282377499 / 1000000000) (Real.log (753989 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13767867 / 62500000) ≤ -Real.log (1000000 / 1246433) ∧
    -Real.log (1000000 / 1246433) ≤ (220285873 / 1000000000) := by
  have h := checkLog_sound (w := (246433 / 2246433)) (n := 12)
    (lo := (13767867 / 62500000)) (hi := (220285873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246433 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246433 / 1000000) = 1/(1000000 / 1246433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13767867 / 62500000) (220285873 / 1000000000) (Real.log (1246433 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1246433 / 1000000) = -Real.log (1000000 / 1246433) := by
    rw [show ((1246433 / 1000000) : ℝ) = ((1000000 / 1246433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141468673 / 500000000) ≤ -Real.log (753567 / 1000000) ∧
    -Real.log (753567 / 1000000) ≤ (282937347 / 1000000000) := by
  have h := checkLog_sound (w := (246433 / 1753567)) (n := 12)
    (lo := (141468673 / 500000000)) (hi := (282937347 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753567) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753567) = 1/(753567 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-282937347 / 1000000000) (-141468673 / 500000000) (Real.log (753567 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (32580511 / 200000000) ≤ -Real.log (500000 / 588461) ∧
    -Real.log (500000 / 588461) ≤ (40725639 / 250000000) := by
  have h := checkLog_sound (w := (88461 / 1088461)) (n := 12)
    (lo := (32580511 / 200000000)) (hi := (40725639 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588461 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588461 / 500000) = 1/(500000 / 588461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (32580511 / 200000000) (40725639 / 250000000) (Real.log (588461 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (588461 / 500000) = -Real.log (500000 / 588461) := by
    rw [show ((588461 / 500000) : ℝ) = ((500000 / 588461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (194704307 / 1000000000) ≤ -Real.log (411539 / 500000) ∧
    -Real.log (411539 / 500000) ≤ (48676077 / 250000000) := by
  have h := checkLog_sound (w := (88461 / 911539)) (n := 12)
    (lo := (194704307 / 1000000000)) (hi := (48676077 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411539) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 411539) = 1/(411539 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-48676077 / 250000000) (-194704307 / 1000000000) (Real.log (411539 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163169317 / 1000000000) ≤ -Real.log (250000 / 294309) ∧
    -Real.log (250000 / 294309) ≤ (81584659 / 500000000) := by
  have h := checkLog_sound (w := (44309 / 544309)) (n := 12)
    (lo := (163169317 / 1000000000)) (hi := (81584659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294309 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294309 / 250000) = 1/(250000 / 294309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163169317 / 1000000000) (81584659 / 500000000) (Real.log (294309 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (294309 / 250000) = -Real.log (250000 / 294309) := by
    rw [show ((294309 / 250000) : ℝ) = ((250000 / 294309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1560687 / 8000000) ≤ -Real.log (205691 / 250000) ∧
    -Real.log (205691 / 250000) ≤ (48771469 / 250000000) := by
  have h := checkLog_sound (w := (44309 / 455691)) (n := 12)
    (lo := (1560687 / 8000000)) (hi := (48771469 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 205691) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 205691) = 1/(205691 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48771469 / 250000000) (-1560687 / 8000000) (Real.log (205691 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (144399633 / 200000000) ≤ -Real.log (50000000000 / 102927120669) ∧
    -Real.log (50000000000 / 102927120669) ≤ (721998167 / 1000000000) := by
  have h := checkLog_sound (w := (2927120669 / 202927120669)) (n := 12)
    (lo := (5770197 / 200000000)) (hi := (14425493 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102927120669 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102927120669 / 100000000000) = 1/(50000000000 / 102927120669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (144399633 / 200000000) (721998167 / 1000000000) (Real.log (102927120669 / 50000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (102927120669 / 50000000000) = -Real.log (50000000000 / 102927120669) := by
    rw [show ((102927120669 / 50000000000) : ℝ) = ((50000000000 / 102927120669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (723329817 / 1000000000) ≤ -Real.log (250000000000 / 515321375187) ∧
    -Real.log (250000000000 / 515321375187) ≤ (723329819 / 1000000000) := by
  have h := checkLog_sound (w := (15321375187 / 1015321375187)) (n := 12)
    (lo := (30182637 / 1000000000)) (hi := (15091319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((515321375187 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(515321375187 / 500000000000) = 1/(250000000000 / 515321375187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (723329817 / 1000000000) (723329819 / 1000000000) (Real.log (515321375187 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (515321375187 / 250000000000) = -Real.log (250000000000 / 515321375187) := by
    rw [show ((515321375187 / 250000000000) : ℝ) = ((250000000000 / 515321375187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (125581187 / 250000000) ≤ -Real.log (500000000000 / 826279295851) ∧
    -Real.log (500000000000 / 826279295851) ≤ (502324749 / 1000000000) := by
  have h := checkLog_sound (w := (326279295851 / 1326279295851)) (n := 12)
    (lo := (125581187 / 250000000)) (hi := (502324749 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826279295851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826279295851 / 500000000000) = 1/(500000000000 / 826279295851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (125581187 / 250000000) (502324749 / 1000000000) (Real.log (826279295851 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (826279295851 / 500000000000) = -Real.log (500000000000 / 826279295851) := by
    rw [show ((826279295851 / 500000000000) : ℝ) = ((500000000000 / 826279295851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (251611609 / 500000000) ≤ -Real.log (500000000000 / 827022016623) ∧
    -Real.log (500000000000 / 827022016623) ≤ (503223219 / 1000000000) := by
  have h := checkLog_sound (w := (327022016623 / 1327022016623)) (n := 12)
    (lo := (251611609 / 500000000)) (hi := (503223219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827022016623 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827022016623 / 500000000000) = 1/(500000000000 / 827022016623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (251611609 / 500000000) (503223219 / 1000000000) (Real.log (827022016623 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (827022016623 / 500000000000) = -Real.log (500000000000 / 827022016623) := by
    rw [show ((827022016623 / 500000000000) : ℝ) = ((500000000000 / 827022016623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (357606863 / 1000000000) ≤ -Real.log (500000000000 / 714951681371) ∧
    -Real.log (500000000000 / 714951681371) ≤ (22350429 / 62500000) := by
  have h := checkLog_sound (w := (214951681371 / 1214951681371)) (n := 12)
    (lo := (357606863 / 1000000000)) (hi := (22350429 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((714951681371 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(714951681371 / 500000000000) = 1/(500000000000 / 714951681371) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (357606863 / 1000000000) (22350429 / 62500000) (Real.log (714951681371 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (714951681371 / 500000000000) = -Real.log (500000000000 / 714951681371) := by
    rw [show ((714951681371 / 500000000000) : ℝ) = ((500000000000 / 714951681371) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358255193 / 1000000000) ≤ -Real.log (125000000000 / 178853839011) ∧
    -Real.log (125000000000 / 178853839011) ≤ (179127597 / 500000000) := by
  have h := checkLog_sound (w := (53853839011 / 303853839011)) (n := 12)
    (lo := (358255193 / 1000000000)) (hi := (179127597 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178853839011 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178853839011 / 125000000000) = 1/(125000000000 / 178853839011) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358255193 / 1000000000) (179127597 / 500000000) (Real.log (178853839011 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (178853839011 / 125000000000) = -Real.log (125000000000 / 178853839011) := by
    rw [show ((178853839011 / 125000000000) : ℝ) = ((125000000000 / 178853839011) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31916557 / 1000000000) ≤ -Real.log (60536712519 / 62500000000) ∧
    -Real.log (60536712519 / 62500000000) ≤ (15958279 / 500000000) := by
  have h := checkLog_sound (w := (1963287481 / 123036712519)) (n := 12)
    (lo := (31916557 / 1000000000)) (hi := (15958279 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60536712519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60536712519) = 1/(60536712519 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-15958279 / 500000000) (-31916557 / 1000000000) (Real.log (60536712519 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31801751 / 1000000000) ≤ -Real.log (242174651479 / 250000000000) ∧
    -Real.log (242174651479 / 250000000000) ≤ (3975219 / 125000000) := by
  have h := checkLog_sound (w := (7825348521 / 492174651479)) (n := 12)
    (lo := (31801751 / 1000000000)) (hi := (3975219 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242174651479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242174651479) = 1/(242174651479 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-3975219 / 125000000) (-31801751 / 1000000000) (Real.log (242174651479 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell164

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell165Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell165
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (11923083 / 40000000) ≤ -Real.log (2560 / 3449) ∧
    -Real.log (2560 / 3449) ≤ (74519269 / 250000000) := by
  have h := checkLog_sound (w := (889 / 6009)) (n := 12)
    (lo := (11923083 / 40000000)) (hi := (74519269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3449 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3449 / 2560) = 1/(2560 / 3449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (11923083 / 40000000) (74519269 / 250000000) (Real.log (3449 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3449 / 2560) = -Real.log (2560 / 3449) := by
    rw [show ((3449 / 2560) : ℝ) = ((2560 / 3449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (26661563 / 62500000) ≤ -Real.log (1671 / 2560) ∧
    -Real.log (1671 / 2560) ≤ (426585009 / 1000000000) := by
  have h := checkLog_sound (w := (889 / 4231)) (n := 12)
    (lo := (26661563 / 62500000)) (hi := (426585009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1671) = 1/(1671 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-426585009 / 1000000000) (-26661563 / 62500000) (Real.log (1671 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (37205259 / 125000000) ≤ -Real.log (1024 / 1379) ∧
    -Real.log (1024 / 1379) ≤ (297642073 / 1000000000) := by
  have h := checkLog_sound (w := (355 / 2403)) (n := 12)
    (lo := (37205259 / 125000000)) (hi := (297642073 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1379 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1379 / 1024) = 1/(1024 / 1379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (37205259 / 125000000) (297642073 / 1000000000) (Real.log (1379 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1379 / 1024) = -Real.log (1024 / 1379) := by
    rw [show ((1379 / 1024) : ℝ) = ((1024 / 1379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (85137549 / 200000000) ≤ -Real.log (669 / 1024) ∧
    -Real.log (669 / 1024) ≤ (212843873 / 500000000) := by
  have h := checkLog_sound (w := (355 / 1693)) (n := 12)
    (lo := (85137549 / 200000000)) (hi := (212843873 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 669) = 1/(669 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-212843873 / 500000000) (-85137549 / 200000000) (Real.log (669 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (220285069 / 1000000000) ≤ -Real.log (31250 / 38951) ∧
    -Real.log (31250 / 38951) ≤ (22028507 / 100000000) := by
  have h := checkLog_sound (w := (7701 / 70201)) (n := 12)
    (lo := (220285069 / 1000000000)) (hi := (22028507 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((38951 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(38951 / 31250) = 1/(31250 / 38951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (220285069 / 1000000000) (22028507 / 100000000) (Real.log (38951 / 31250)) := by
  have h := reflection_log_5_neg
  have he : Real.log (38951 / 31250) = -Real.log (31250 / 38951) := by
    rw [show ((38951 / 31250) : ℝ) = ((31250 / 38951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (282936019 / 1000000000) ≤ -Real.log (23549 / 31250) ∧
    -Real.log (23549 / 31250) ≤ (14146801 / 50000000) := by
  have h := checkLog_sound (w := (7701 / 54799)) (n := 12)
    (lo := (282936019 / 1000000000)) (hi := (14146801 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 23549) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 23549) = 1/(23549 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-14146801 / 50000000) (-282936019 / 1000000000) (Real.log (23549 / 31250)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (110311789 / 500000000) ≤ -Real.log (500000 / 623427) ∧
    -Real.log (500000 / 623427) ≤ (220623579 / 1000000000) := by
  have h := checkLog_sound (w := (123427 / 1123427)) (n := 12)
    (lo := (110311789 / 500000000)) (hi := (220623579 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623427 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623427 / 500000) = 1/(500000 / 623427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (110311789 / 500000000) (220623579 / 1000000000) (Real.log (623427 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (623427 / 500000) = -Real.log (500000 / 623427) := by
    rw [show ((623427 / 500000) : ℝ) = ((500000 / 623427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (141748089 / 500000000) ≤ -Real.log (376573 / 500000) ∧
    -Real.log (376573 / 500000) ≤ (283496179 / 1000000000) := by
  have h := checkLog_sound (w := (123427 / 876573)) (n := 12)
    (lo := (141748089 / 500000000)) (hi := (283496179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376573) = 1/(376573 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-283496179 / 1000000000) (-141748089 / 500000000) (Real.log (376573 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40792117 / 250000000) ≤ -Real.log (200000 / 235447) ∧
    -Real.log (200000 / 235447) ≤ (163168469 / 1000000000) := by
  have h := checkLog_sound (w := (35447 / 435447)) (n := 12)
    (lo := (40792117 / 250000000)) (hi := (163168469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235447 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235447 / 200000) = 1/(200000 / 235447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40792117 / 250000000) (163168469 / 1000000000) (Real.log (235447 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (235447 / 200000) = -Real.log (200000 / 235447) := by
    rw [show ((235447 / 200000) : ℝ) = ((200000 / 235447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (195084659 / 1000000000) ≤ -Real.log (164553 / 200000) ∧
    -Real.log (164553 / 200000) ≤ (9754233 / 50000000) := by
  have h := checkLog_sound (w := (35447 / 364553)) (n := 12)
    (lo := (195084659 / 1000000000)) (hi := (9754233 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164553) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164553) = 1/(164553 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-9754233 / 50000000) (-195084659 / 1000000000) (Real.log (164553 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20429501 / 125000000) ≤ -Real.log (20000 / 23551) ∧
    -Real.log (20000 / 23551) ≤ (163436009 / 1000000000) := by
  have h := checkLog_sound (w := (3551 / 43551)) (n := 12)
    (lo := (20429501 / 125000000)) (hi := (163436009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23551 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23551 / 20000) = 1/(20000 / 23551) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20429501 / 125000000) (163436009 / 1000000000) (Real.log (23551 / 20000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (23551 / 20000) = -Real.log (20000 / 23551) := by
    rw [show ((23551 / 20000) : ℝ) = ((20000 / 23551) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48866897 / 250000000) ≤ -Real.log (16449 / 20000) ∧
    -Real.log (16449 / 20000) ≤ (195467589 / 1000000000) := by
  have h := checkLog_sound (w := (3551 / 36449)) (n := 12)
    (lo := (48866897 / 250000000)) (hi := (195467589 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 16449) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 16449) = 1/(16449 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-195467589 / 1000000000) (-48866897 / 250000000) (Real.log (16449 / 20000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (723329817 / 1000000000) ≤ -Real.log (500000000000 / 1030642750373) ∧
    -Real.log (500000000000 / 1030642750373) ≤ (723329819 / 1000000000) := by
  have h := checkLog_sound (w := (30642750373 / 2030642750373)) (n := 12)
    (lo := (30182637 / 1000000000)) (hi := (15091319 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1030642750373 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1030642750373 / 1000000000000) = 1/(500000000000 / 1030642750373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (723329817 / 1000000000) (723329819 / 1000000000) (Real.log (1030642750373 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1030642750373 / 500000000000) = -Real.log (500000000000 / 1030642750373) := by
    rw [show ((1030642750373 / 500000000000) : ℝ) = ((500000000000 / 1030642750373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (724662083 / 1000000000) ≤ -Real.log (250000000000 / 516008378217) ∧
    -Real.log (250000000000 / 516008378217) ≤ (144932417 / 200000000) := by
  have h := checkLog_sound (w := (16008378217 / 1016008378217)) (n := 12)
    (lo := (31514903 / 1000000000)) (hi := (3939363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516008378217 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516008378217 / 500000000000) = 1/(250000000000 / 516008378217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (724662083 / 1000000000) (144932417 / 200000000) (Real.log (516008378217 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (516008378217 / 250000000000) = -Real.log (250000000000 / 516008378217) := by
    rw [show ((516008378217 / 250000000000) : ℝ) = ((250000000000 / 516008378217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (503221089 / 1000000000) ≤ -Real.log (500000000000 / 827020255637) ∧
    -Real.log (500000000000 / 827020255637) ≤ (50322109 / 100000000) := by
  have h := checkLog_sound (w := (327020255637 / 1327020255637)) (n := 12)
    (lo := (503221089 / 1000000000)) (hi := (50322109 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827020255637 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827020255637 / 500000000000) = 1/(500000000000 / 827020255637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (503221089 / 1000000000) (50322109 / 100000000) (Real.log (827020255637 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827020255637 / 500000000000) = -Real.log (500000000000 / 827020255637) := by
    rw [show ((827020255637 / 500000000000) : ℝ) = ((500000000000 / 827020255637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (504119757 / 1000000000) ≤ -Real.log (15625000000 / 25867618961) ∧
    -Real.log (15625000000 / 25867618961) ≤ (252059879 / 500000000) := by
  have h := checkLog_sound (w := (10242618961 / 41492618961)) (n := 12)
    (lo := (504119757 / 1000000000)) (hi := (252059879 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25867618961 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25867618961 / 15625000000) = 1/(15625000000 / 25867618961) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (504119757 / 1000000000) (252059879 / 500000000) (Real.log (25867618961 / 15625000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (25867618961 / 15625000000) = -Real.log (15625000000 / 25867618961) := by
    rw [show ((25867618961 / 15625000000) : ℝ) = ((15625000000 / 25867618961) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (44781641 / 125000000) ≤ -Real.log (500000000000 / 715413878811) ∧
    -Real.log (500000000000 / 715413878811) ≤ (358253129 / 1000000000) := by
  have h := checkLog_sound (w := (215413878811 / 1215413878811)) (n := 12)
    (lo := (44781641 / 125000000)) (hi := (358253129 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((715413878811 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(715413878811 / 500000000000) = 1/(500000000000 / 715413878811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (44781641 / 125000000) (358253129 / 1000000000) (Real.log (715413878811 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (715413878811 / 500000000000) = -Real.log (500000000000 / 715413878811) := by
    rw [show ((715413878811 / 500000000000) : ℝ) = ((500000000000 / 715413878811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (358903597 / 1000000000) ≤ -Real.log (250000000000 / 357939692383) ∧
    -Real.log (250000000000 / 357939692383) ≤ (179451799 / 500000000) := by
  have h := checkLog_sound (w := (107939692383 / 607939692383)) (n := 12)
    (lo := (358903597 / 1000000000)) (hi := (179451799 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((357939692383 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(357939692383 / 250000000000) = 1/(250000000000 / 357939692383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (358903597 / 1000000000) (179451799 / 500000000) (Real.log (357939692383 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (357939692383 / 250000000000) = -Real.log (250000000000 / 357939692383) := by
    rw [show ((357939692383 / 250000000000) : ℝ) = ((250000000000 / 357939692383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32031579 / 1000000000) ≤ -Real.log (387390399 / 400000000) ∧
    -Real.log (387390399 / 400000000) ≤ (1601579 / 50000000) := by
  have h := checkLog_sound (w := (12609601 / 787390399)) (n := 12)
    (lo := (32031579 / 1000000000)) (hi := (1601579 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((400000000 / 387390399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(400000000 / 387390399) = 1/(387390399 / 400000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-1601579 / 50000000) (-32031579 / 1000000000) (Real.log (387390399 / 400000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (31916191 / 1000000000) ≤ -Real.log (38743510191 / 40000000000) ∧
    -Real.log (38743510191 / 40000000000) ≤ (997381 / 31250000) := by
  have h := checkLog_sound (w := (1256489809 / 78743510191)) (n := 12)
    (lo := (31916191 / 1000000000)) (hi := (997381 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38743510191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38743510191) = 1/(38743510191 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-997381 / 31250000) (-31916191 / 1000000000) (Real.log (38743510191 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell165

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell166Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell166
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (298511889 / 1000000000) ≤ -Real.log (5120 / 6901) ∧
    -Real.log (5120 / 6901) ≤ (29851189 / 100000000) := by
  have h := checkLog_sound (w := (1781 / 12021)) (n := 12)
    (lo := (298511889 / 1000000000)) (hi := (29851189 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6901 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6901 / 5120) = 1/(5120 / 6901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (298511889 / 1000000000) (29851189 / 100000000) (Real.log (6901 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6901 / 5120) = -Real.log (5120 / 6901) := by
    rw [show ((6901 / 5120) : ℝ) = ((5120 / 6901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (213741539 / 500000000) ≤ -Real.log (3339 / 5120) ∧
    -Real.log (3339 / 5120) ≤ (427483079 / 1000000000) := by
  have h := checkLog_sound (w := (1781 / 8459)) (n := 12)
    (lo := (213741539 / 500000000)) (hi := (427483079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3339) = 1/(3339 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-427483079 / 1000000000) (-213741539 / 500000000) (Real.log (3339 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (11923083 / 40000000) ≤ -Real.log (2560 / 3449) ∧
    -Real.log (2560 / 3449) ≤ (74519269 / 250000000) := by
  have h := checkLog_sound (w := (889 / 6009)) (n := 12)
    (lo := (11923083 / 40000000)) (hi := (74519269 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3449 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3449 / 2560) = 1/(2560 / 3449) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (11923083 / 40000000) (74519269 / 250000000) (Real.log (3449 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3449 / 2560) = -Real.log (2560 / 3449) := by
    rw [show ((3449 / 2560) : ℝ) = ((2560 / 3449) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (26661563 / 62500000) ≤ -Real.log (1671 / 2560) ∧
    -Real.log (1671 / 2560) ≤ (426585009 / 1000000000) := by
  have h := checkLog_sound (w := (889 / 4231)) (n := 12)
    (lo := (26661563 / 62500000)) (hi := (426585009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1671) = 1/(1671 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-426585009 / 1000000000) (-26661563 / 62500000) (Real.log (1671 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (27577847 / 125000000) ≤ -Real.log (1000000 / 1246853) ∧
    -Real.log (1000000 / 1246853) ≤ (220622777 / 1000000000) := by
  have h := checkLog_sound (w := (246853 / 2246853)) (n := 12)
    (lo := (27577847 / 125000000)) (hi := (220622777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1246853 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1246853 / 1000000) = 1/(1000000 / 1246853) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (27577847 / 125000000) (220622777 / 1000000000) (Real.log (1246853 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1246853 / 1000000) = -Real.log (1000000 / 1246853) := by
    rw [show ((1246853 / 1000000) : ℝ) = ((1000000 / 1246853) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (283494851 / 1000000000) ≤ -Real.log (753147 / 1000000) ∧
    -Real.log (753147 / 1000000) ≤ (70873713 / 250000000) := by
  have h := checkLog_sound (w := (246853 / 1753147)) (n := 12)
    (lo := (283494851 / 1000000000)) (hi := (70873713 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 753147) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 753147) = 1/(753147 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-70873713 / 250000000) (-283494851 / 1000000000) (Real.log (753147 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (220961171 / 1000000000) ≤ -Real.log (40000 / 49891) ∧
    -Real.log (40000 / 49891) ≤ (55240293 / 250000000) := by
  have h := checkLog_sound (w := (9891 / 89891)) (n := 12)
    (lo := (220961171 / 1000000000)) (hi := (55240293 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((49891 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(49891 / 40000) = 1/(40000 / 49891) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (220961171 / 1000000000) (55240293 / 250000000) (Real.log (49891 / 40000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (49891 / 40000) = -Real.log (40000 / 49891) := by
    rw [show ((49891 / 40000) : ℝ) = ((40000 / 49891) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (284055323 / 1000000000) ≤ -Real.log (30109 / 40000) ∧
    -Real.log (30109 / 40000) ≤ (71013831 / 250000000) := by
  have h := checkLog_sound (w := (9891 / 70109)) (n := 12)
    (lo := (284055323 / 1000000000)) (hi := (71013831 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 30109) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 30109) = 1/(30109 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-71013831 / 250000000) (-284055323 / 1000000000) (Real.log (30109 / 40000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (163435159 / 1000000000) ≤ -Real.log (1000000 / 1177549) ∧
    -Real.log (1000000 / 1177549) ≤ (4085879 / 25000000) := by
  have h := checkLog_sound (w := (177549 / 2177549)) (n := 12)
    (lo := (163435159 / 1000000000)) (hi := (4085879 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177549 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177549 / 1000000) = 1/(1000000 / 1177549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (163435159 / 1000000000) (4085879 / 25000000) (Real.log (1177549 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1177549 / 1000000) = -Real.log (1000000 / 1177549) := by
    rw [show ((1177549 / 1000000) : ℝ) = ((1000000 / 1177549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (48866593 / 250000000) ≤ -Real.log (822451 / 1000000) ∧
    -Real.log (822451 / 1000000) ≤ (195466373 / 1000000000) := by
  have h := checkLog_sound (w := (177549 / 1822451)) (n := 12)
    (lo := (48866593 / 250000000)) (hi := (195466373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822451) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822451) = 1/(822451 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-195466373 / 1000000000) (-48866593 / 250000000) (Real.log (822451 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163701779 / 1000000000) ≤ -Real.log (1000000 / 1177863) ∧
    -Real.log (1000000 / 1177863) ≤ (8185089 / 50000000) := by
  have h := checkLog_sound (w := (177863 / 2177863)) (n := 12)
    (lo := (163701779 / 1000000000)) (hi := (8185089 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177863 / 1000000) = 1/(1000000 / 1177863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163701779 / 1000000000) (8185089 / 50000000) (Real.log (1177863 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1177863 / 1000000) = -Real.log (1000000 / 1177863) := by
    rw [show ((1177863 / 1000000) : ℝ) = ((1000000 / 1177863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (195848231 / 1000000000) ≤ -Real.log (822137 / 1000000) ∧
    -Real.log (822137 / 1000000) ≤ (24481029 / 125000000) := by
  have h := checkLog_sound (w := (177863 / 1822137)) (n := 12)
    (lo := (195848231 / 1000000000)) (hi := (24481029 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822137) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822137) = 1/(822137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-24481029 / 125000000) (-195848231 / 1000000000) (Real.log (822137 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (724662083 / 1000000000) ≤ -Real.log (500000000000 / 1032016756433) ∧
    -Real.log (500000000000 / 1032016756433) ≤ (144932417 / 200000000) := by
  have h := checkLog_sound (w := (32016756433 / 2032016756433)) (n := 12)
    (lo := (31514903 / 1000000000)) (hi := (3939363 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1032016756433 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1032016756433 / 1000000000000) = 1/(500000000000 / 1032016756433) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (724662083 / 1000000000) (144932417 / 200000000) (Real.log (1032016756433 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1032016756433 / 500000000000) = -Real.log (500000000000 / 1032016756433) := by
    rw [show ((1032016756433 / 500000000000) : ℝ) = ((500000000000 / 1032016756433) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (725994967 / 1000000000) ≤ -Real.log (500000000000 / 1033393231507) ∧
    -Real.log (500000000000 / 1033393231507) ≤ (725994969 / 1000000000) := by
  have h := checkLog_sound (w := (33393231507 / 2033393231507)) (n := 12)
    (lo := (32847787 / 1000000000)) (hi := (8211947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033393231507 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033393231507 / 1000000000000) = 1/(500000000000 / 1033393231507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (725994967 / 1000000000) (725994969 / 1000000000) (Real.log (1033393231507 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1033393231507 / 500000000000) = -Real.log (500000000000 / 1033393231507) := by
    rw [show ((1033393231507 / 500000000000) : ℝ) = ((500000000000 / 1033393231507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (504117627 / 1000000000) ≤ -Real.log (500000000000 / 827762043797) ∧
    -Real.log (500000000000 / 827762043797) ≤ (126029407 / 250000000) := by
  have h := checkLog_sound (w := (327762043797 / 1327762043797)) (n := 12)
    (lo := (504117627 / 1000000000)) (hi := (126029407 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827762043797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827762043797 / 500000000000) = 1/(500000000000 / 827762043797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (504117627 / 1000000000) (126029407 / 250000000) (Real.log (827762043797 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (827762043797 / 500000000000) = -Real.log (500000000000 / 827762043797) := by
    rw [show ((827762043797 / 500000000000) : ℝ) = ((500000000000 / 827762043797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (101003299 / 200000000) ≤ -Real.log (10000000000 / 16570128533) ∧
    -Real.log (10000000000 / 16570128533) ≤ (31563531 / 62500000) := by
  have h := checkLog_sound (w := (6570128533 / 26570128533)) (n := 12)
    (lo := (101003299 / 200000000)) (hi := (31563531 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16570128533 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(16570128533 / 10000000000) = 1/(10000000000 / 16570128533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (101003299 / 200000000) (31563531 / 62500000) (Real.log (16570128533 / 10000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (16570128533 / 10000000000) = -Real.log (10000000000 / 16570128533) := by
    rw [show ((16570128533 / 10000000000) : ℝ) = ((10000000000 / 16570128533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (89725383 / 250000000) ≤ -Real.log (125000000000 / 178969476601) ∧
    -Real.log (125000000000 / 178969476601) ≤ (358901533 / 1000000000) := by
  have h := checkLog_sound (w := (53969476601 / 303969476601)) (n := 12)
    (lo := (89725383 / 250000000)) (hi := (358901533 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178969476601 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178969476601 / 125000000000) = 1/(125000000000 / 178969476601) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (89725383 / 250000000) (358901533 / 1000000000) (Real.log (178969476601 / 125000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (178969476601 / 125000000000) = -Real.log (125000000000 / 178969476601) := by
    rw [show ((178969476601 / 125000000000) : ℝ) = ((125000000000 / 178969476601) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (35955001 / 100000000) ≤ -Real.log (500000000000 / 716342288451) ∧
    -Real.log (500000000000 / 716342288451) ≤ (359550011 / 1000000000) := by
  have h := checkLog_sound (w := (216342288451 / 1216342288451)) (n := 12)
    (lo := (35955001 / 100000000)) (hi := (359550011 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716342288451 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716342288451 / 500000000000) = 1/(500000000000 / 716342288451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (35955001 / 100000000) (359550011 / 1000000000) (Real.log (716342288451 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (716342288451 / 500000000000) = -Real.log (500000000000 / 716342288451) := by
    rw [show ((716342288451 / 500000000000) : ℝ) = ((500000000000 / 716342288451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (32146451 / 1000000000) ≤ -Real.log (968364753231 / 1000000000000) ∧
    -Real.log (968364753231 / 1000000000000) ≤ (8036613 / 250000000) := by
  have h := checkLog_sound (w := (31635246769 / 1968364753231)) (n := 12)
    (lo := (32146451 / 1000000000)) (hi := (8036613 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968364753231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968364753231) = 1/(968364753231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-8036613 / 250000000) (-32146451 / 1000000000) (Real.log (968364753231 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8007803 / 250000000) ≤ -Real.log (968476352599 / 1000000000000) ∧
    -Real.log (968476352599 / 1000000000000) ≤ (32031213 / 1000000000) := by
  have h := checkLog_sound (w := (31523647401 / 1968476352599)) (n := 12)
    (lo := (8007803 / 250000000)) (hi := (32031213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968476352599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968476352599) = 1/(968476352599 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32031213 / 1000000000) (-8007803 / 250000000) (Real.log (968476352599 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell166

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell167Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell167
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (149473257 / 500000000) ≤ -Real.log (640 / 863) ∧
    -Real.log (640 / 863) ≤ (59789303 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1503)) (n := 12)
    (lo := (149473257 / 500000000)) (hi := (59789303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863 / 640) = 1/(640 / 863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (149473257 / 500000000) (59789303 / 200000000) (Real.log (863 / 640)) := by
  have h := reflection_log_1_neg
  have he : Real.log (863 / 640) = -Real.log (640 / 863) := by
    rw [show ((863 / 640) : ℝ) = ((640 / 863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (214190977 / 500000000) ≤ -Real.log (417 / 640) ∧
    -Real.log (417 / 640) ≤ (85676391 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 417) = 1/(417 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-85676391 / 200000000) (-214190977 / 500000000) (Real.log (417 / 640)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (298511889 / 1000000000) ≤ -Real.log (5120 / 6901) ∧
    -Real.log (5120 / 6901) ≤ (29851189 / 100000000) := by
  have h := checkLog_sound (w := (1781 / 12021)) (n := 12)
    (lo := (298511889 / 1000000000)) (hi := (29851189 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6901 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6901 / 5120) = 1/(5120 / 6901) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (298511889 / 1000000000) (29851189 / 100000000) (Real.log (6901 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6901 / 5120) = -Real.log (5120 / 6901) := by
    rw [show ((6901 / 5120) : ℝ) = ((5120 / 6901) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (213741539 / 500000000) ≤ -Real.log (3339 / 5120) ∧
    -Real.log (3339 / 5120) ≤ (427483079 / 1000000000) := by
  have h := checkLog_sound (w := (1781 / 8459)) (n := 12)
    (lo := (213741539 / 500000000)) (hi := (427483079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3339) = 1/(3339 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-427483079 / 1000000000) (-213741539 / 500000000) (Real.log (3339 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (220960369 / 1000000000) ≤ -Real.log (500000 / 623637) ∧
    -Real.log (500000 / 623637) ≤ (22096037 / 100000000) := by
  have h := checkLog_sound (w := (123637 / 1123637)) (n := 12)
    (lo := (220960369 / 1000000000)) (hi := (22096037 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((623637 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(623637 / 500000) = 1/(500000 / 623637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (220960369 / 1000000000) (22096037 / 100000000) (Real.log (623637 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (623637 / 500000) = -Real.log (500000 / 623637) := by
    rw [show ((623637 / 500000) : ℝ) = ((500000 / 623637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (56810799 / 200000000) ≤ -Real.log (376363 / 500000) ∧
    -Real.log (376363 / 500000) ≤ (71013499 / 250000000) := by
  have h := checkLog_sound (w := (123637 / 876363)) (n := 12)
    (lo := (56810799 / 200000000)) (hi := (71013499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 376363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 376363) = 1/(376363 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-71013499 / 250000000) (-56810799 / 200000000) (Real.log (376363 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (4425973 / 20000000) ≤ -Real.log (62500 / 77981) ∧
    -Real.log (62500 / 77981) ≤ (221298651 / 1000000000) := by
  have h := checkLog_sound (w := (15481 / 140481)) (n := 12)
    (lo := (4425973 / 20000000)) (hi := (221298651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77981 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77981 / 62500) = 1/(62500 / 77981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (4425973 / 20000000) (221298651 / 1000000000) (Real.log (77981 / 62500)) := by
  have h := reflection_log_7_neg
  have he : Real.log (77981 / 62500) = -Real.log (62500 / 77981) := by
    rw [show ((77981 / 62500) : ℝ) = ((62500 / 77981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (284614781 / 1000000000) ≤ -Real.log (47019 / 62500) ∧
    -Real.log (47019 / 62500) ≤ (142307391 / 500000000) := by
  have h := checkLog_sound (w := (15481 / 109519)) (n := 12)
    (lo := (284614781 / 1000000000)) (hi := (142307391 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 47019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 47019) = 1/(47019 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-142307391 / 500000000) (-284614781 / 1000000000) (Real.log (47019 / 62500)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (16370093 / 100000000) ≤ -Real.log (500000 / 588931) ∧
    -Real.log (500000 / 588931) ≤ (163700931 / 1000000000) := by
  have h := checkLog_sound (w := (88931 / 1088931)) (n := 12)
    (lo := (16370093 / 100000000)) (hi := (163700931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588931 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588931 / 500000) = 1/(500000 / 588931) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (16370093 / 100000000) (163700931 / 1000000000) (Real.log (588931 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (588931 / 500000) = -Real.log (500000 / 588931) := by
    rw [show ((588931 / 500000) : ℝ) = ((500000 / 588931) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (97923507 / 500000000) ≤ -Real.log (411069 / 500000) ∧
    -Real.log (411069 / 500000) ≤ (39169403 / 200000000) := by
  have h := checkLog_sound (w := (88931 / 911069)) (n := 12)
    (lo := (97923507 / 500000000)) (hi := (39169403 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 411069) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 411069) = 1/(411069 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-39169403 / 200000000) (-97923507 / 500000000) (Real.log (411069 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (163967479 / 1000000000) ≤ -Real.log (15625 / 18409) ∧
    -Real.log (15625 / 18409) ≤ (4099187 / 25000000) := by
  have h := checkLog_sound (w := (1392 / 17017)) (n := 12)
    (lo := (163967479 / 1000000000)) (hi := (4099187 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((18409 / 15625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(18409 / 15625) = 1/(15625 / 18409) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (163967479 / 1000000000) (4099187 / 25000000) (Real.log (18409 / 15625)) := by
  have h := reflection_log_11_neg
  have he : Real.log (18409 / 15625) = -Real.log (15625 / 18409) := by
    rw [show ((18409 / 15625) : ℝ) = ((15625 / 18409) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (98114509 / 500000000) ≤ -Real.log (12841 / 15625) ∧
    -Real.log (12841 / 15625) ≤ (196229019 / 1000000000) := by
  have h := checkLog_sound (w := (1392 / 14233)) (n := 12)
    (lo := (98114509 / 500000000)) (hi := (196229019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625 / 12841) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625 / 12841) = 1/(12841 / 15625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196229019 / 1000000000) (-98114509 / 500000000) (Real.log (12841 / 15625)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (725994967 / 1000000000) ≤ -Real.log (250000000000 / 516696615753) ∧
    -Real.log (250000000000 / 516696615753) ≤ (725994969 / 1000000000) := by
  have h := checkLog_sound (w := (16696615753 / 1016696615753)) (n := 12)
    (lo := (32847787 / 1000000000)) (hi := (8211947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((516696615753 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(516696615753 / 500000000000) = 1/(250000000000 / 516696615753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (725994967 / 1000000000) (725994969 / 1000000000) (Real.log (516696615753 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (516696615753 / 250000000000) = -Real.log (250000000000 / 516696615753) := by
    rw [show ((516696615753 / 250000000000) : ℝ) = ((250000000000 / 516696615753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (181832117 / 250000000) ≤ -Real.log (100000000000 / 206954436451) ∧
    -Real.log (100000000000 / 206954436451) ≤ (72732847 / 100000000) := by
  have h := checkLog_sound (w := (6954436451 / 406954436451)) (n := 12)
    (lo := (4272661 / 125000000)) (hi := (34181289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206954436451 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(206954436451 / 200000000000) = 1/(100000000000 / 206954436451) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (181832117 / 250000000) (72732847 / 100000000) (Real.log (206954436451 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (206954436451 / 100000000000) = -Real.log (100000000000 / 206954436451) := by
    rw [show ((206954436451 / 100000000000) : ℝ) = ((100000000000 / 206954436451) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (101002873 / 200000000) ≤ -Real.log (250000000000 / 414252330861) ∧
    -Real.log (250000000000 / 414252330861) ≤ (252507183 / 500000000) := by
  have h := checkLog_sound (w := (164252330861 / 664252330861)) (n := 12)
    (lo := (101002873 / 200000000)) (hi := (252507183 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414252330861 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414252330861 / 250000000000) = 1/(250000000000 / 414252330861) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (101002873 / 200000000) (252507183 / 500000000) (Real.log (414252330861 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (414252330861 / 250000000000) = -Real.log (250000000000 / 414252330861) := by
    rw [show ((414252330861 / 250000000000) : ℝ) = ((250000000000 / 414252330861) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (505913431 / 1000000000) ≤ -Real.log (50000000000 / 82924987771) ∧
    -Real.log (50000000000 / 82924987771) ≤ (63239179 / 125000000) := by
  have h := checkLog_sound (w := (32924987771 / 132924987771)) (n := 12)
    (lo := (505913431 / 1000000000)) (hi := (63239179 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82924987771 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(82924987771 / 50000000000) = 1/(50000000000 / 82924987771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (505913431 / 1000000000) (63239179 / 125000000) (Real.log (82924987771 / 50000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (82924987771 / 50000000000) = -Real.log (50000000000 / 82924987771) := by
    rw [show ((82924987771 / 50000000000) : ℝ) = ((50000000000 / 82924987771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (71909589 / 200000000) ≤ -Real.log (500000000000 / 716340808963) ∧
    -Real.log (500000000000 / 716340808963) ≤ (179773973 / 500000000) := by
  have h := checkLog_sound (w := (216340808963 / 1216340808963)) (n := 12)
    (lo := (71909589 / 200000000)) (hi := (179773973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716340808963 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716340808963 / 500000000000) = 1/(500000000000 / 716340808963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (71909589 / 200000000) (179773973 / 500000000) (Real.log (716340808963 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (716340808963 / 500000000000) = -Real.log (500000000000 / 716340808963) := by
    rw [show ((716340808963 / 500000000000) : ℝ) = ((500000000000 / 716340808963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180098249 / 500000000) ≤ -Real.log (25000000000 / 35840277237) ∧
    -Real.log (25000000000 / 35840277237) ≤ (360196499 / 1000000000) := by
  have h := checkLog_sound (w := (10840277237 / 60840277237)) (n := 12)
    (lo := (180098249 / 500000000)) (hi := (360196499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((35840277237 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(35840277237 / 25000000000) = 1/(25000000000 / 35840277237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180098249 / 500000000) (360196499 / 1000000000) (Real.log (35840277237 / 25000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (35840277237 / 25000000000) = -Real.log (25000000000 / 35840277237) := by
    rw [show ((35840277237 / 25000000000) : ℝ) = ((25000000000 / 35840277237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (16130769 / 500000000) ≤ -Real.log (236389969 / 244140625) ∧
    -Real.log (236389969 / 244140625) ≤ (32261539 / 1000000000) := by
  have h := checkLog_sound (w := (3875328 / 240265297)) (n := 12)
    (lo := (16130769 / 500000000)) (hi := (32261539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((244140625 / 236389969) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(244140625 / 236389969) = 1/(236389969 / 244140625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32261539 / 1000000000) (-16130769 / 500000000) (Real.log (236389969 / 244140625)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (8036521 / 250000000) ≤ -Real.log (242091277239 / 250000000000) ∧
    -Real.log (242091277239 / 250000000000) ≤ (6429217 / 200000000) := by
  have h := checkLog_sound (w := (7908722761 / 492091277239)) (n := 12)
    (lo := (8036521 / 250000000)) (hi := (6429217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242091277239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242091277239) = 1/(242091277239 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6429217 / 200000000) (-8036521 / 250000000) (Real.log (242091277239 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell167

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell168Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell168
open GeneralCK GeneralCK.Certificates.Reflection GeneralCK.Certificates.Mixed GeneralCK.Reflection

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

theorem reflection_log_1_neg : (299380951 / 1000000000) ≤ -Real.log (5120 / 6907) ∧
    -Real.log (5120 / 6907) ≤ (37422619 / 125000000) := by
  have h := checkLog_sound (w := (1787 / 12027)) (n := 12)
    (lo := (299380951 / 1000000000)) (hi := (37422619 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6907 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6907 / 5120) = 1/(5120 / 6907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (299380951 / 1000000000) (37422619 / 125000000) (Real.log (6907 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6907 / 5120) = -Real.log (5120 / 6907) := by
    rw [show ((6907 / 5120) : ℝ) = ((5120 / 6907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (429281639 / 1000000000) ≤ -Real.log (3333 / 5120) ∧
    -Real.log (3333 / 5120) ≤ (10732041 / 25000000) := by
  have h := checkLog_sound (w := (1787 / 8453)) (n := 12)
    (lo := (429281639 / 1000000000)) (hi := (10732041 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3333) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3333) = 1/(3333 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-10732041 / 25000000) (-429281639 / 1000000000) (Real.log (3333 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (149473257 / 500000000) ≤ -Real.log (640 / 863) ∧
    -Real.log (640 / 863) ≤ (59789303 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1503)) (n := 12)
    (lo := (149473257 / 500000000)) (hi := (59789303 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((863 / 640) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(863 / 640) = 1/(640 / 863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (149473257 / 500000000) (59789303 / 200000000) (Real.log (863 / 640)) := by
  have h := reflection_log_3_neg
  have he : Real.log (863 / 640) = -Real.log (640 / 863) := by
    rw [show ((863 / 640) : ℝ) = ((640 / 863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (214190977 / 500000000) ≤ -Real.log (417 / 640) ∧
    -Real.log (417 / 640) ≤ (85676391 / 200000000) := by
  have h := checkLog_sound (w := (223 / 1057)) (n := 12)
    (lo := (214190977 / 500000000)) (hi := (85676391 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((640 / 417) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(640 / 417) = 1/(417 / 640) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-85676391 / 200000000) (-214190977 / 500000000) (Real.log (417 / 640)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (221297849 / 1000000000) ≤ -Real.log (200000 / 249539) ∧
    -Real.log (200000 / 249539) ≤ (4425957 / 20000000) := by
  have h := checkLog_sound (w := (49539 / 449539)) (n := 12)
    (lo := (221297849 / 1000000000)) (hi := (4425957 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((249539 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(249539 / 200000) = 1/(200000 / 249539) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (221297849 / 1000000000) (4425957 / 20000000) (Real.log (249539 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (249539 / 200000) = -Real.log (200000 / 249539) := by
    rw [show ((249539 / 200000) : ℝ) = ((200000 / 249539) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (71153363 / 250000000) ≤ -Real.log (150461 / 200000) ∧
    -Real.log (150461 / 200000) ≤ (284613453 / 1000000000) := by
  have h := checkLog_sound (w := (49539 / 350461)) (n := 12)
    (lo := (71153363 / 250000000)) (hi := (284613453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 150461) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 150461) = 1/(150461 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-284613453 / 1000000000) (-71153363 / 250000000) (Real.log (150461 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13852301 / 62500000) ≤ -Real.log (500000 / 624059) ∧
    -Real.log (500000 / 624059) ≤ (221636817 / 1000000000) := by
  have h := checkLog_sound (w := (124059 / 1124059)) (n := 12)
    (lo := (13852301 / 62500000)) (hi := (221636817 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((624059 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(624059 / 500000) = 1/(500000 / 624059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13852301 / 62500000) (221636817 / 1000000000) (Real.log (624059 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (624059 / 500000) = -Real.log (500000 / 624059) := by
    rw [show ((624059 / 500000) : ℝ) = ((500000 / 624059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (142587941 / 500000000) ≤ -Real.log (375941 / 500000) ∧
    -Real.log (375941 / 500000) ≤ (285175883 / 1000000000) := by
  have h := checkLog_sound (w := (124059 / 875941)) (n := 12)
    (lo := (142587941 / 500000000)) (hi := (285175883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 375941) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 375941) = 1/(375941 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-285175883 / 1000000000) (-142587941 / 500000000) (Real.log (375941 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (163966631 / 1000000000) ≤ -Real.log (40000 / 47127) ∧
    -Real.log (40000 / 47127) ≤ (20495829 / 125000000) := by
  have h := checkLog_sound (w := (7127 / 87127)) (n := 12)
    (lo := (163966631 / 1000000000)) (hi := (20495829 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47127 / 40000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(47127 / 40000) = 1/(40000 / 47127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (163966631 / 1000000000) (20495829 / 125000000) (Real.log (47127 / 40000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (47127 / 40000) = -Real.log (40000 / 47127) := by
    rw [show ((47127 / 40000) : ℝ) = ((40000 / 47127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (196227801 / 1000000000) ≤ -Real.log (32873 / 40000) ∧
    -Real.log (32873 / 40000) ≤ (98113901 / 500000000) := by
  have h := checkLog_sound (w := (7127 / 72873)) (n := 12)
    (lo := (196227801 / 1000000000)) (hi := (98113901 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000 / 32873) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000 / 32873) = 1/(32873 / 40000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-98113901 / 500000000) (-196227801 / 1000000000) (Real.log (32873 / 40000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (164233957 / 1000000000) ≤ -Real.log (100000 / 117849) ∧
    -Real.log (100000 / 117849) ≤ (82116979 / 500000000) := by
  have h := checkLog_sound (w := (17849 / 217849)) (n := 12)
    (lo := (164233957 / 1000000000)) (hi := (82116979 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117849 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117849 / 100000) = 1/(100000 / 117849) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (164233957 / 1000000000) (82116979 / 500000000) (Real.log (117849 / 100000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (117849 / 100000) = -Real.log (100000 / 117849) := by
    rw [show ((117849 / 100000) : ℝ) = ((100000 / 117849) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (6144099 / 31250000) ≤ -Real.log (82151 / 100000) ∧
    -Real.log (82151 / 100000) ≤ (196611169 / 1000000000) := by
  have h := checkLog_sound (w := (17849 / 182151)) (n := 12)
    (lo := (6144099 / 31250000)) (hi := (196611169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82151) = 1/(82151 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-196611169 / 1000000000) (-6144099 / 31250000) (Real.log (82151 / 100000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (181832117 / 250000000) ≤ -Real.log (250000000000 / 517386091127) ∧
    -Real.log (250000000000 / 517386091127) ≤ (72732847 / 100000000) := by
  have h := checkLog_sound (w := (17386091127 / 1017386091127)) (n := 12)
    (lo := (4272661 / 125000000)) (hi := (34181289 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((517386091127 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(517386091127 / 500000000000) = 1/(250000000000 / 517386091127) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (181832117 / 250000000) (72732847 / 100000000) (Real.log (517386091127 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (517386091127 / 250000000000) = -Real.log (250000000000 / 517386091127) := by
    rw [show ((517386091127 / 250000000000) : ℝ) = ((250000000000 / 517386091127) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (72866259 / 100000000) ≤ -Real.log (250000000000 / 518076807681) ∧
    -Real.log (250000000000 / 518076807681) ≤ (11385353 / 15625000) := by
  have h := checkLog_sound (w := (18076807681 / 1018076807681)) (n := 12)
    (lo := (3551541 / 100000000)) (hi := (35515411 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((518076807681 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(518076807681 / 500000000000) = 1/(250000000000 / 518076807681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (72866259 / 100000000) (11385353 / 15625000) (Real.log (518076807681 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (518076807681 / 250000000000) = -Real.log (250000000000 / 518076807681) := by
    rw [show ((518076807681 / 250000000000) : ℝ) = ((250000000000 / 518076807681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (505911301 / 1000000000) ≤ -Real.log (250000000000 / 414624055403) ∧
    -Real.log (250000000000 / 414624055403) ≤ (252955651 / 500000000) := by
  have h := checkLog_sound (w := (164624055403 / 664624055403)) (n := 12)
    (lo := (505911301 / 1000000000)) (hi := (252955651 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((414624055403 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(414624055403 / 250000000000) = 1/(250000000000 / 414624055403) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (505911301 / 1000000000) (252955651 / 500000000) (Real.log (414624055403 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (414624055403 / 250000000000) = -Real.log (250000000000 / 414624055403) := by
    rw [show ((414624055403 / 250000000000) : ℝ) = ((250000000000 / 414624055403) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (253406349 / 500000000) ≤ -Real.log (500000000000 / 829995930213) ∧
    -Real.log (500000000000 / 829995930213) ≤ (506812699 / 1000000000) := by
  have h := checkLog_sound (w := (329995930213 / 1329995930213)) (n := 12)
    (lo := (253406349 / 500000000)) (hi := (506812699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((829995930213 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(829995930213 / 500000000000) = 1/(500000000000 / 829995930213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (253406349 / 500000000) (506812699 / 1000000000) (Real.log (829995930213 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (829995930213 / 500000000000) = -Real.log (500000000000 / 829995930213) := by
    rw [show ((829995930213 / 500000000000) : ℝ) = ((500000000000 / 829995930213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (360194433 / 1000000000) ≤ -Real.log (4000000000 / 5734432513) ∧
    -Real.log (4000000000 / 5734432513) ≤ (180097217 / 500000000) := by
  have h := checkLog_sound (w := (1734432513 / 9734432513)) (n := 12)
    (lo := (360194433 / 1000000000)) (hi := (180097217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5734432513 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5734432513 / 4000000000) = 1/(4000000000 / 5734432513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (360194433 / 1000000000) (180097217 / 500000000) (Real.log (5734432513 / 4000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (5734432513 / 4000000000) = -Real.log (4000000000 / 5734432513) := by
    rw [show ((5734432513 / 4000000000) : ℝ) = ((4000000000 / 5734432513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (180422563 / 500000000) ≤ -Real.log (500000000000 / 717270635781) ∧
    -Real.log (500000000000 / 717270635781) ≤ (360845127 / 1000000000) := by
  have h := checkLog_sound (w := (217270635781 / 1217270635781)) (n := 12)
    (lo := (180422563 / 500000000)) (hi := (360845127 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717270635781 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717270635781 / 500000000000) = 1/(500000000000 / 717270635781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (180422563 / 500000000) (360845127 / 1000000000) (Real.log (717270635781 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (717270635781 / 500000000000) = -Real.log (500000000000 / 717270635781) := by
    rw [show ((717270635781 / 500000000000) : ℝ) = ((500000000000 / 717270635781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3237721 / 100000000) ≤ -Real.log (9681413199 / 10000000000) ∧
    -Real.log (9681413199 / 10000000000) ≤ (32377211 / 1000000000) := by
  have h := checkLog_sound (w := (318586801 / 19681413199)) (n := 12)
    (lo := (3237721 / 100000000)) (hi := (32377211 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9681413199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9681413199) = 1/(9681413199 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-32377211 / 1000000000) (-3237721 / 100000000) (Real.log (9681413199 / 10000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (3226117 / 100000000) ≤ -Real.log (1549205871 / 1600000000) ∧
    -Real.log (1549205871 / 1600000000) ≤ (32261171 / 1000000000) := by
  have h := checkLog_sound (w := (50794129 / 3149205871)) (n := 12)
    (lo := (3226117 / 100000000)) (hi := (32261171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1600000000 / 1549205871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1600000000 / 1549205871) = 1/(1549205871 / 1600000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-32261171 / 1000000000) (-3226117 / 100000000) (Real.log (1549205871 / 1600000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell168

end


