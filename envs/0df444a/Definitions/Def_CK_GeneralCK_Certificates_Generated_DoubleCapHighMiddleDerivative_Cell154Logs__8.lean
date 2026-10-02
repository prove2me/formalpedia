-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell154Logs__8
-- name    : CK_GeneralCK_Certificates_Generated_DoubleCapHighMiddleDerivative_Cell154Logs__8
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T16:37:48.940989+00:00
-- url     : https://prove2.me/theorems/766ee6c6-d310-48ae-8e47-255075145417
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell154Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell155…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell154Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell155Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell156Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell157Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell158Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell159Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell160Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell161Logs)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell154Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell155Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell156Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell157Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell158Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell159Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell160Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell161Logs)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell154Logs (+7 modules: GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell155Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell156Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell157Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell158Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell159Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell160Logs, GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell161Logs) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell154Logs (+7 modules: GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell155Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell156Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell157Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell158Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell159Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell160Logs, GeneralCK/Certificates/Generated/DoubleCapHighMiddleDerivative/Cell161Logs).lean)

import Definitions.Def_CK_GeneralCK_PureGapDoubleCapBiasChecker

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell154Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell154
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

theorem reflection_log_1_neg : (183301 / 625000) ≤ -Real.log (1024 / 1373) ∧
    -Real.log (1024 / 1373) ≤ (293281601 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 2397)) (n := 12)
    (lo := (183301 / 625000)) (hi := (293281601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1024) = 1/(1024 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (183301 / 625000) (293281601 / 1000000000) (Real.log (1373 / 1024)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1373 / 1024) = -Real.log (1024 / 1373) := by
    rw [show ((1373 / 1024) : ℝ) = ((1024 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208379557 / 500000000) ≤ -Real.log (675 / 1024) ∧
    -Real.log (675 / 1024) ≤ (83351823 / 200000000) := by
  have h := checkLog_sound (w := (349 / 1699)) (n := 12)
    (lo := (208379557 / 500000000)) (hi := (83351823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 675) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 675) = 1/(675 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-83351823 / 200000000) (-208379557 / 500000000) (Real.log (675 / 1024)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (58568901 / 200000000) ≤ -Real.log (2560 / 3431) ∧
    -Real.log (2560 / 3431) ≤ (146422253 / 500000000) := by
  have h := checkLog_sound (w := (871 / 5991)) (n := 12)
    (lo := (58568901 / 200000000)) (hi := (146422253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3431 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3431 / 2560) = 1/(2560 / 3431) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (58568901 / 200000000) (146422253 / 500000000) (Real.log (3431 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3431 / 2560) = -Real.log (2560 / 3431) := by
    rw [show ((3431 / 2560) : ℝ) = ((2560 / 3431) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (20793531 / 50000000) ≤ -Real.log (1689 / 2560) ∧
    -Real.log (1689 / 2560) ≤ (415870621 / 1000000000) := by
  have h := checkLog_sound (w := (871 / 4249)) (n := 12)
    (lo := (20793531 / 50000000)) (hi := (415870621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1689) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1689) = 1/(1689 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-415870621 / 1000000000) (-20793531 / 50000000) (Real.log (1689 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (43312549 / 200000000) ≤ -Real.log (1000000 / 1241801) ∧
    -Real.log (1000000 / 1241801) ≤ (108281373 / 500000000) := by
  have h := checkLog_sound (w := (241801 / 2241801)) (n := 12)
    (lo := (43312549 / 200000000)) (hi := (108281373 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1241801 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1241801 / 1000000) = 1/(1000000 / 1241801) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (43312549 / 200000000) (108281373 / 500000000) (Real.log (1241801 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1241801 / 1000000) = -Real.log (1000000 / 1241801) := by
    rw [show ((1241801 / 1000000) : ℝ) = ((1000000 / 1241801) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138404697 / 500000000) ≤ -Real.log (758199 / 1000000) ∧
    -Real.log (758199 / 1000000) ≤ (55361879 / 200000000) := by
  have h := checkLog_sound (w := (241801 / 1758199)) (n := 12)
    (lo := (138404697 / 500000000)) (hi := (55361879 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 758199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 758199) = 1/(758199 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-55361879 / 200000000) (-138404697 / 500000000) (Real.log (758199 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (54225629 / 250000000) ≤ -Real.log (1000000 / 1242223) ∧
    -Real.log (1000000 / 1242223) ≤ (216902517 / 1000000000) := by
  have h := checkLog_sound (w := (242223 / 2242223)) (n := 12)
    (lo := (54225629 / 250000000)) (hi := (216902517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242223 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242223 / 1000000) = 1/(1000000 / 1242223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (54225629 / 250000000) (216902517 / 1000000000) (Real.log (1242223 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1242223 / 1000000) = -Real.log (1000000 / 1242223) := by
    rw [show ((1242223 / 1000000) : ℝ) = ((1000000 / 1242223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (277366131 / 1000000000) ≤ -Real.log (757777 / 1000000) ∧
    -Real.log (757777 / 1000000) ≤ (69341533 / 250000000) := by
  have h := checkLog_sound (w := (242223 / 1757777)) (n := 12)
    (lo := (277366131 / 1000000000)) (hi := (69341533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757777) = 1/(757777 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-69341533 / 250000000) (-277366131 / 1000000000) (Real.log (757777 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (160241237 / 1000000000) ≤ -Real.log (500000 / 586897) ∧
    -Real.log (500000 / 586897) ≤ (80120619 / 500000000) := by
  have h := checkLog_sound (w := (86897 / 1086897)) (n := 12)
    (lo := (160241237 / 1000000000)) (hi := (80120619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((586897 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(586897 / 500000) = 1/(500000 / 586897) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (160241237 / 1000000000) (80120619 / 500000000) (Real.log (586897 / 500000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (586897 / 500000) = -Real.log (500000 / 586897) := by
    rw [show ((586897 / 500000) : ℝ) = ((500000 / 586897) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (190911141 / 1000000000) ≤ -Real.log (413103 / 500000) ∧
    -Real.log (413103 / 500000) ≤ (95455571 / 500000000) := by
  have h := checkLog_sound (w := (86897 / 913103)) (n := 12)
    (lo := (190911141 / 1000000000)) (hi := (95455571 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 413103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 413103) = 1/(413103 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95455571 / 500000000) (-190911141 / 1000000000) (Real.log (413103 / 500000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (16050871 / 100000000) ≤ -Real.log (250000 / 293527) ∧
    -Real.log (250000 / 293527) ≤ (160508711 / 1000000000) := by
  have h := checkLog_sound (w := (43527 / 543527)) (n := 12)
    (lo := (16050871 / 100000000)) (hi := (160508711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293527 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293527 / 250000) = 1/(250000 / 293527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (16050871 / 100000000) (160508711 / 1000000000) (Real.log (293527 / 250000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (293527 / 250000) = -Real.log (250000 / 293527) := by
    rw [show ((293527 / 250000) : ℝ) = ((250000 / 293527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (1494463 / 7812500) ≤ -Real.log (206473 / 250000) ∧
    -Real.log (206473 / 250000) ≤ (38258253 / 200000000) := by
  have h := checkLog_sound (w := (43527 / 456473)) (n := 12)
    (lo := (1494463 / 7812500)) (hi := (38258253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206473) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206473) = 1/(206473 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-38258253 / 200000000) (-1494463 / 7812500) (Real.log (206473 / 250000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (5669721 / 8000000) ≤ -Real.log (125000000000 / 253922439313) ∧
    -Real.log (125000000000 / 253922439313) ≤ (708715127 / 1000000000) := by
  have h := checkLog_sound (w := (3922439313 / 503922439313)) (n := 12)
    (lo := (3113589 / 200000000)) (hi := (7783973 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((253922439313 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(253922439313 / 250000000000) = 1/(125000000000 / 253922439313) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (5669721 / 8000000) (708715127 / 1000000000) (Real.log (253922439313 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (253922439313 / 125000000000) = -Real.log (125000000000 / 253922439313) := by
    rw [show ((253922439313 / 125000000000) : ℝ) = ((125000000000 / 253922439313) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355020357 / 500000000) ≤ -Real.log (250000000000 / 508518518519) ∧
    -Real.log (250000000000 / 508518518519) ≤ (177510179 / 250000000) := by
  have h := checkLog_sound (w := (8518518519 / 1008518518519)) (n := 12)
    (lo := (8446767 / 500000000)) (hi := (3378707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((508518518519 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(508518518519 / 500000000000) = 1/(250000000000 / 508518518519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (355020357 / 500000000) (177510179 / 250000000) (Real.log (508518518519 / 250000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (508518518519 / 250000000000) = -Real.log (250000000000 / 508518518519) := by
    rw [show ((508518518519 / 250000000000) : ℝ) = ((250000000000 / 508518518519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (24668607 / 50000000) ≤ -Real.log (125000000000 / 204728738761) ∧
    -Real.log (125000000000 / 204728738761) ≤ (493372141 / 1000000000) := by
  have h := checkLog_sound (w := (79728738761 / 329728738761)) (n := 12)
    (lo := (24668607 / 50000000)) (hi := (493372141 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204728738761 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204728738761 / 125000000000) = 1/(125000000000 / 204728738761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (24668607 / 50000000) (493372141 / 1000000000) (Real.log (204728738761 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (204728738761 / 125000000000) = -Real.log (125000000000 / 204728738761) := by
    rw [show ((204728738761 / 125000000000) : ℝ) = ((125000000000 / 204728738761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (61783581 / 125000000) ≤ -Real.log (500000000000 / 819649448321) ∧
    -Real.log (500000000000 / 819649448321) ≤ (494268649 / 1000000000) := by
  have h := checkLog_sound (w := (319649448321 / 1319649448321)) (n := 12)
    (lo := (61783581 / 125000000)) (hi := (494268649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819649448321 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819649448321 / 500000000000) = 1/(500000000000 / 819649448321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (61783581 / 125000000) (494268649 / 1000000000) (Real.log (819649448321 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (819649448321 / 500000000000) = -Real.log (500000000000 / 819649448321) := by
    rw [show ((819649448321 / 500000000000) : ℝ) = ((500000000000 / 819649448321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (351152379 / 1000000000) ≤ -Real.log (50000000000 / 71035189771) ∧
    -Real.log (50000000000 / 71035189771) ≤ (17557619 / 50000000) := by
  have h := checkLog_sound (w := (21035189771 / 121035189771)) (n := 12)
    (lo := (351152379 / 1000000000)) (hi := (17557619 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71035189771 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71035189771 / 50000000000) = 1/(50000000000 / 71035189771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (351152379 / 1000000000) (17557619 / 50000000) (Real.log (71035189771 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71035189771 / 50000000000) = -Real.log (50000000000 / 71035189771) := by
    rw [show ((71035189771 / 50000000000) : ℝ) = ((50000000000 / 71035189771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (175899987 / 500000000) ≤ -Real.log (250000000000 / 355406033719) ∧
    -Real.log (250000000000 / 355406033719) ≤ (14071999 / 40000000) := by
  have h := checkLog_sound (w := (105406033719 / 605406033719)) (n := 12)
    (lo := (175899987 / 500000000)) (hi := (14071999 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((355406033719 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(355406033719 / 250000000000) = 1/(250000000000 / 355406033719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (175899987 / 500000000) (14071999 / 40000000) (Real.log (355406033719 / 250000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (355406033719 / 250000000000) = -Real.log (250000000000 / 355406033719) := by
    rw [show ((355406033719 / 250000000000) : ℝ) = ((250000000000 / 355406033719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15391277 / 500000000) ≤ -Real.log (60605400271 / 62500000000) ∧
    -Real.log (60605400271 / 62500000000) ≤ (6156511 / 200000000) := by
  have h := checkLog_sound (w := (1894599729 / 123105400271)) (n := 12)
    (lo := (15391277 / 500000000)) (hi := (6156511 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60605400271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60605400271) = 1/(60605400271 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6156511 / 200000000) (-15391277 / 500000000) (Real.log (60605400271 / 62500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1916869 / 62500000) ≤ -Real.log (242448911391 / 250000000000) ∧
    -Real.log (242448911391 / 250000000000) ≤ (6133981 / 200000000) := by
  have h := checkLog_sound (w := (7551088609 / 492448911391)) (n := 12)
    (lo := (1916869 / 62500000)) (hi := (6133981 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242448911391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242448911391) = 1/(242448911391 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6133981 / 200000000) (-1916869 / 62500000) (Real.log (242448911391 / 250000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell154

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell155Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell155
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

theorem reflection_log_1_neg : (293718503 / 1000000000) ≤ -Real.log (1280 / 1717) ∧
    -Real.log (1280 / 1717) ≤ (36714813 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2997)) (n := 12)
    (lo := (293718503 / 1000000000)) (hi := (36714813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1717 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1717 / 1280) = 1/(1280 / 1717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (293718503 / 1000000000) (36714813 / 125000000) (Real.log (1717 / 1280)) := by
  have h := reflection_log_1_neg
  have he : Real.log (1717 / 1280) = -Real.log (1280 / 1717) := by
    rw [show ((1717 / 1280) : ℝ) = ((1280 / 1717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (208824199 / 500000000) ≤ -Real.log (843 / 1280) ∧
    -Real.log (843 / 1280) ≤ (417648399 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 2123)) (n := 12)
    (lo := (208824199 / 500000000)) (hi := (417648399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 843) = 1/(843 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-417648399 / 1000000000) (-208824199 / 500000000) (Real.log (843 / 1280)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (183301 / 625000) ≤ -Real.log (1024 / 1373) ∧
    -Real.log (1024 / 1373) ≤ (293281601 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 2397)) (n := 12)
    (lo := (183301 / 625000)) (hi := (293281601 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1373 / 1024) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1373 / 1024) = 1/(1024 / 1373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (183301 / 625000) (293281601 / 1000000000) (Real.log (1373 / 1024)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1373 / 1024) = -Real.log (1024 / 1373) := by
    rw [show ((1373 / 1024) : ℝ) = ((1024 / 1373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208379557 / 500000000) ≤ -Real.log (675 / 1024) ∧
    -Real.log (675 / 1024) ≤ (83351823 / 200000000) := by
  have h := checkLog_sound (w := (349 / 1699)) (n := 12)
    (lo := (208379557 / 500000000)) (hi := (83351823 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1024 / 675) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1024 / 675) = 1/(675 / 1024) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-83351823 / 200000000) (-208379557 / 500000000) (Real.log (675 / 1024)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (216901711 / 1000000000) ≤ -Real.log (500000 / 621111) ∧
    -Real.log (500000 / 621111) ≤ (13556357 / 62500000) := by
  have h := checkLog_sound (w := (121111 / 1121111)) (n := 12)
    (lo := (216901711 / 1000000000)) (hi := (13556357 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621111 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621111 / 500000) = 1/(500000 / 621111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (216901711 / 1000000000) (13556357 / 62500000) (Real.log (621111 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (621111 / 500000) = -Real.log (500000 / 621111) := by
    rw [show ((621111 / 500000) : ℝ) = ((500000 / 621111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (69341203 / 250000000) ≤ -Real.log (378889 / 500000) ∧
    -Real.log (378889 / 500000) ≤ (277364813 / 1000000000) := by
  have h := checkLog_sound (w := (121111 / 878889)) (n := 12)
    (lo := (69341203 / 250000000)) (hi := (277364813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378889) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378889) = 1/(378889 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277364813 / 1000000000) (-69341203 / 250000000) (Real.log (378889 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (217241367 / 1000000000) ≤ -Real.log (250000 / 310661) ∧
    -Real.log (250000 / 310661) ≤ (27155171 / 125000000) := by
  have h := checkLog_sound (w := (60661 / 560661)) (n := 12)
    (lo := (217241367 / 1000000000)) (hi := (27155171 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310661 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310661 / 250000) = 1/(250000 / 310661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (217241367 / 1000000000) (27155171 / 125000000) (Real.log (310661 / 250000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (310661 / 250000) = -Real.log (250000 / 310661) := by
    rw [show ((310661 / 250000) : ℝ) = ((250000 / 310661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (138960929 / 500000000) ≤ -Real.log (189339 / 250000) ∧
    -Real.log (189339 / 250000) ≤ (277921859 / 1000000000) := by
  have h := checkLog_sound (w := (60661 / 439339)) (n := 12)
    (lo := (138960929 / 500000000)) (hi := (277921859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 189339) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 189339) = 1/(189339 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-277921859 / 1000000000) (-138960929 / 500000000) (Real.log (189339 / 250000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (80253929 / 500000000) ≤ -Real.log (1000000 / 1174107) ∧
    -Real.log (1000000 / 1174107) ≤ (160507859 / 1000000000) := by
  have h := checkLog_sound (w := (174107 / 2174107)) (n := 12)
    (lo := (80253929 / 500000000)) (hi := (160507859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174107 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174107 / 1000000) = 1/(1000000 / 1174107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (80253929 / 500000000) (160507859 / 1000000000) (Real.log (1174107 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1174107 / 1000000) = -Real.log (1000000 / 1174107) := by
    rw [show ((1174107 / 1000000) : ℝ) = ((1000000 / 1174107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (191290053 / 1000000000) ≤ -Real.log (825893 / 1000000) ∧
    -Real.log (825893 / 1000000) ≤ (95645027 / 500000000) := by
  have h := checkLog_sound (w := (174107 / 1825893)) (n := 12)
    (lo := (191290053 / 1000000000)) (hi := (95645027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825893) = 1/(825893 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-95645027 / 500000000) (-191290053 / 1000000000) (Real.log (825893 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20096801 / 125000000) ≤ -Real.log (50000 / 58721) ∧
    -Real.log (50000 / 58721) ≤ (160774409 / 1000000000) := by
  have h := checkLog_sound (w := (8721 / 108721)) (n := 12)
    (lo := (20096801 / 125000000)) (hi := (160774409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58721 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58721 / 50000) = 1/(50000 / 58721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20096801 / 125000000) (160774409 / 1000000000) (Real.log (58721 / 50000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (58721 / 50000) = -Real.log (50000 / 58721) := by
    rw [show ((58721 / 50000) : ℝ) = ((50000 / 58721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (191669109 / 1000000000) ≤ -Real.log (41279 / 50000) ∧
    -Real.log (41279 / 50000) ≤ (19166911 / 100000000) := by
  have h := checkLog_sound (w := (8721 / 91279)) (n := 12)
    (lo := (191669109 / 1000000000)) (hi := (19166911 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 41279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 41279) = 1/(41279 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-19166911 / 100000000) (-191669109 / 1000000000) (Real.log (41279 / 50000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (355020357 / 500000000) ≤ -Real.log (500000000000 / 1017037037037) ∧
    -Real.log (500000000000 / 1017037037037) ≤ (177510179 / 250000000) := by
  have h := checkLog_sound (w := (17037037037 / 2017037037037)) (n := 12)
    (lo := (8446767 / 500000000)) (hi := (3378707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1017037037037 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1017037037037 / 1000000000000) = 1/(500000000000 / 1017037037037) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (355020357 / 500000000) (177510179 / 250000000) (Real.log (1017037037037 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1017037037037 / 500000000000) = -Real.log (500000000000 / 1017037037037) := by
    rw [show ((1017037037037 / 500000000000) : ℝ) = ((500000000000 / 1017037037037) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (355683451 / 500000000) ≤ -Real.log (500000000000 / 1018386714117) ∧
    -Real.log (500000000000 / 1018386714117) ≤ (88920863 / 125000000) := by
  have h := checkLog_sound (w := (18386714117 / 2018386714117)) (n := 12)
    (lo := (9109861 / 500000000)) (hi := (18219723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1018386714117 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1018386714117 / 1000000000000) = 1/(500000000000 / 1018386714117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (355683451 / 500000000) (88920863 / 125000000) (Real.log (1018386714117 / 500000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1018386714117 / 500000000000) = -Real.log (500000000000 / 1018386714117) := by
    rw [show ((1018386714117 / 500000000000) : ℝ) = ((500000000000 / 1018386714117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (494266523 / 1000000000) ≤ -Real.log (15625000000 / 25613990839) ∧
    -Real.log (15625000000 / 25613990839) ≤ (123566631 / 250000000) := by
  have h := checkLog_sound (w := (9988990839 / 41238990839)) (n := 12)
    (lo := (494266523 / 1000000000)) (hi := (123566631 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25613990839 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25613990839 / 15625000000) = 1/(15625000000 / 25613990839) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (494266523 / 1000000000) (123566631 / 250000000) (Real.log (25613990839 / 15625000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (25613990839 / 15625000000) = -Real.log (15625000000 / 25613990839) := by
    rw [show ((25613990839 / 15625000000) : ℝ) = ((15625000000 / 25613990839) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (247581613 / 500000000) ≤ -Real.log (250000000000 / 410191508353) ∧
    -Real.log (250000000000 / 410191508353) ≤ (495163227 / 1000000000) := by
  have h := checkLog_sound (w := (160191508353 / 660191508353)) (n := 12)
    (lo := (247581613 / 500000000)) (hi := (495163227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410191508353 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410191508353 / 250000000000) = 1/(250000000000 / 410191508353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (247581613 / 500000000) (495163227 / 1000000000) (Real.log (410191508353 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (410191508353 / 250000000000) = -Real.log (250000000000 / 410191508353) := by
    rw [show ((410191508353 / 250000000000) : ℝ) = ((250000000000 / 410191508353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (43974739 / 125000000) ≤ -Real.log (500000000000 / 710810601373) ∧
    -Real.log (500000000000 / 710810601373) ≤ (351797913 / 1000000000) := by
  have h := checkLog_sound (w := (210810601373 / 1210810601373)) (n := 12)
    (lo := (43974739 / 125000000)) (hi := (351797913 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((710810601373 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(710810601373 / 500000000000) = 1/(500000000000 / 710810601373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (43974739 / 125000000) (351797913 / 1000000000) (Real.log (710810601373 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (710810601373 / 500000000000) = -Real.log (500000000000 / 710810601373) := by
    rw [show ((710810601373 / 500000000000) : ℝ) = ((500000000000 / 710810601373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (176221759 / 500000000) ≤ -Real.log (500000000000 / 711269652851) ∧
    -Real.log (500000000000 / 711269652851) ≤ (352443519 / 1000000000) := by
  have h := checkLog_sound (w := (211269652851 / 1211269652851)) (n := 12)
    (lo := (176221759 / 500000000)) (hi := (352443519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711269652851 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711269652851 / 500000000000) = 1/(500000000000 / 711269652851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (176221759 / 500000000) (352443519 / 1000000000) (Real.log (711269652851 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (711269652851 / 500000000000) = -Real.log (500000000000 / 711269652851) := by
    rw [show ((711269652851 / 500000000000) : ℝ) = ((500000000000 / 711269652851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (308947 / 10000000) ≤ -Real.log (2423944159 / 2500000000) ∧
    -Real.log (2423944159 / 2500000000) ≤ (30894701 / 1000000000) := by
  have h := checkLog_sound (w := (76055841 / 4923944159)) (n := 12)
    (lo := (308947 / 10000000)) (hi := (30894701 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2423944159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2423944159) = 1/(2423944159 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-30894701 / 1000000000) (-308947 / 10000000) (Real.log (2423944159 / 2500000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6156439 / 200000000) ≤ -Real.log (969686752551 / 1000000000000) ∧
    -Real.log (969686752551 / 1000000000000) ≤ (7695549 / 250000000) := by
  have h := checkLog_sound (w := (30313247449 / 1969686752551)) (n := 12)
    (lo := (6156439 / 200000000)) (hi := (7695549 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969686752551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969686752551) = 1/(969686752551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-7695549 / 250000000) (-6156439 / 200000000) (Real.log (969686752551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell155

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell156Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell156
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

theorem reflection_log_1_neg : (18384701 / 62500000) ≤ -Real.log (5120 / 6871) ∧
    -Real.log (5120 / 6871) ≤ (294155217 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 11991)) (n := 12)
    (lo := (18384701 / 62500000)) (hi := (294155217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6871 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6871 / 5120) = 1/(5120 / 6871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (18384701 / 62500000) (294155217 / 1000000000) (Real.log (6871 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6871 / 5120) = -Real.log (5120 / 6871) := by
    rw [show ((6871 / 5120) : ℝ) = ((5120 / 6871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (209269237 / 500000000) ≤ -Real.log (3369 / 5120) ∧
    -Real.log (3369 / 5120) ≤ (16741539 / 40000000) := by
  have h := checkLog_sound (w := (1751 / 8489)) (n := 12)
    (lo := (209269237 / 500000000)) (hi := (16741539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3369) = 1/(3369 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-16741539 / 40000000) (-209269237 / 500000000) (Real.log (3369 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (293718503 / 1000000000) ≤ -Real.log (1280 / 1717) ∧
    -Real.log (1280 / 1717) ≤ (36714813 / 125000000) := by
  have h := checkLog_sound (w := (437 / 2997)) (n := 12)
    (lo := (293718503 / 1000000000)) (hi := (36714813 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1717 / 1280) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1717 / 1280) = 1/(1280 / 1717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (293718503 / 1000000000) (36714813 / 125000000) (Real.log (1717 / 1280)) := by
  have h := reflection_log_3_neg
  have he : Real.log (1717 / 1280) = -Real.log (1280 / 1717) := by
    rw [show ((1717 / 1280) : ℝ) = ((1280 / 1717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (208824199 / 500000000) ≤ -Real.log (843 / 1280) ∧
    -Real.log (843 / 1280) ≤ (417648399 / 1000000000) := by
  have h := checkLog_sound (w := (437 / 2123)) (n := 12)
    (lo := (208824199 / 500000000)) (hi := (417648399 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1280 / 843) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1280 / 843) = 1/(843 / 1280) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-417648399 / 1000000000) (-208824199 / 500000000) (Real.log (843 / 1280)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (108620281 / 500000000) ≤ -Real.log (1000000 / 1242643) ∧
    -Real.log (1000000 / 1242643) ≤ (217240563 / 1000000000) := by
  have h := checkLog_sound (w := (242643 / 2242643)) (n := 12)
    (lo := (108620281 / 500000000)) (hi := (217240563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1242643 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1242643 / 1000000) = 1/(1000000 / 1242643) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (108620281 / 500000000) (217240563 / 1000000000) (Real.log (1242643 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1242643 / 1000000) = -Real.log (1000000 / 1242643) := by
    rw [show ((1242643 / 1000000) : ℝ) = ((1000000 / 1242643) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (138960269 / 500000000) ≤ -Real.log (757357 / 1000000) ∧
    -Real.log (757357 / 1000000) ≤ (277920539 / 1000000000) := by
  have h := checkLog_sound (w := (242643 / 1757357)) (n := 12)
    (lo := (138960269 / 500000000)) (hi := (277920539 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 757357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 757357) = 1/(757357 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-277920539 / 1000000000) (-138960269 / 500000000) (Real.log (757357 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (27197513 / 125000000) ≤ -Real.log (200000 / 248613) ∧
    -Real.log (200000 / 248613) ≤ (43516021 / 200000000) := by
  have h := checkLog_sound (w := (48613 / 448613)) (n := 12)
    (lo := (27197513 / 125000000)) (hi := (43516021 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248613 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248613 / 200000) = 1/(200000 / 248613) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (27197513 / 125000000) (43516021 / 200000000) (Real.log (248613 / 200000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (248613 / 200000) = -Real.log (200000 / 248613) := by
    rw [show ((248613 / 200000) : ℝ) = ((200000 / 248613) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (139238947 / 500000000) ≤ -Real.log (151387 / 200000) ∧
    -Real.log (151387 / 200000) ≤ (55695579 / 200000000) := by
  have h := checkLog_sound (w := (48613 / 351387)) (n := 12)
    (lo := (139238947 / 500000000)) (hi := (55695579 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151387) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151387) = 1/(151387 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55695579 / 200000000) (-139238947 / 500000000) (Real.log (151387 / 200000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (160773557 / 1000000000) ≤ -Real.log (1000000 / 1174419) ∧
    -Real.log (1000000 / 1174419) ≤ (80386779 / 500000000) := by
  have h := checkLog_sound (w := (174419 / 2174419)) (n := 12)
    (lo := (160773557 / 1000000000)) (hi := (80386779 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174419 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174419 / 1000000) = 1/(1000000 / 1174419) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (160773557 / 1000000000) (80386779 / 500000000) (Real.log (1174419 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1174419 / 1000000) = -Real.log (1000000 / 1174419) := by
    rw [show ((1174419 / 1000000) : ℝ) = ((1000000 / 1174419) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (95833949 / 500000000) ≤ -Real.log (825581 / 1000000) ∧
    -Real.log (825581 / 1000000) ≤ (191667899 / 1000000000) := by
  have h := checkLog_sound (w := (174419 / 1825581)) (n := 12)
    (lo := (95833949 / 500000000)) (hi := (191667899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825581) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825581) = 1/(825581 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-191667899 / 1000000000) (-95833949 / 500000000) (Real.log (825581 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (161040887 / 1000000000) ≤ -Real.log (1000000 / 1174733) ∧
    -Real.log (1000000 / 1174733) ≤ (20130111 / 125000000) := by
  have h := checkLog_sound (w := (174733 / 2174733)) (n := 12)
    (lo := (161040887 / 1000000000)) (hi := (20130111 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1174733 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1174733 / 1000000) = 1/(1000000 / 1174733) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (161040887 / 1000000000) (20130111 / 125000000) (Real.log (1174733 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1174733 / 1000000) = -Real.log (1000000 / 1174733) := by
    rw [show ((1174733 / 1000000) : ℝ) = ((1000000 / 1174733) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48012077 / 250000000) ≤ -Real.log (825267 / 1000000) ∧
    -Real.log (825267 / 1000000) ≤ (192048309 / 1000000000) := by
  have h := checkLog_sound (w := (174733 / 1825267)) (n := 12)
    (lo := (48012077 / 250000000)) (hi := (192048309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 825267) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 825267) = 1/(825267 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-192048309 / 1000000000) (-48012077 / 250000000) (Real.log (825267 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (355683451 / 500000000) ≤ -Real.log (125000000000 / 254596678529) ∧
    -Real.log (125000000000 / 254596678529) ≤ (88920863 / 125000000) := by
  have h := checkLog_sound (w := (4596678529 / 504596678529)) (n := 12)
    (lo := (9109861 / 500000000)) (hi := (18219723 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((254596678529 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(254596678529 / 250000000000) = 1/(125000000000 / 254596678529) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (355683451 / 500000000) (88920863 / 125000000) (Real.log (254596678529 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (254596678529 / 125000000000) = -Real.log (125000000000 / 254596678529) := by
    rw [show ((254596678529 / 125000000000) : ℝ) = ((125000000000 / 254596678529) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (712693691 / 1000000000) ≤ -Real.log (100000000000 / 203947758979) ∧
    -Real.log (100000000000 / 203947758979) ≤ (712693693 / 1000000000) := by
  have h := checkLog_sound (w := (3947758979 / 403947758979)) (n := 12)
    (lo := (19546511 / 1000000000)) (hi := (1221657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((203947758979 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(203947758979 / 200000000000) = 1/(100000000000 / 203947758979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (712693691 / 1000000000) (712693693 / 1000000000) (Real.log (203947758979 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (203947758979 / 100000000000) = -Real.log (100000000000 / 203947758979) := by
    rw [show ((203947758979 / 100000000000) : ℝ) = ((100000000000 / 203947758979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (495161101 / 1000000000) ≤ -Real.log (31250000000 / 51273829581) ∧
    -Real.log (31250000000 / 51273829581) ≤ (247580551 / 500000000) := by
  have h := checkLog_sound (w := (20023829581 / 82523829581)) (n := 12)
    (lo := (495161101 / 1000000000)) (hi := (247580551 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((51273829581 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(51273829581 / 31250000000) = 1/(31250000000 / 51273829581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (495161101 / 1000000000) (247580551 / 500000000) (Real.log (51273829581 / 31250000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (51273829581 / 31250000000) = -Real.log (31250000000 / 51273829581) := by
    rw [show ((51273829581 / 31250000000) : ℝ) = ((31250000000 / 51273829581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (248028999 / 500000000) ≤ -Real.log (250000000000 / 410558700549) ∧
    -Real.log (250000000000 / 410558700549) ≤ (496057999 / 1000000000) := by
  have h := checkLog_sound (w := (160558700549 / 660558700549)) (n := 12)
    (lo := (248028999 / 500000000)) (hi := (496057999 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410558700549 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410558700549 / 250000000000) = 1/(250000000000 / 410558700549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (248028999 / 500000000) (496057999 / 1000000000) (Real.log (410558700549 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (410558700549 / 250000000000) = -Real.log (250000000000 / 410558700549) := by
    rw [show ((410558700549 / 250000000000) : ℝ) = ((250000000000 / 410558700549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (70488291 / 200000000) ≤ -Real.log (500000000000 / 711268185677) ∧
    -Real.log (500000000000 / 711268185677) ≤ (22027591 / 62500000) := by
  have h := checkLog_sound (w := (211268185677 / 1211268185677)) (n := 12)
    (lo := (70488291 / 200000000)) (hi := (22027591 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711268185677 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711268185677 / 500000000000) = 1/(500000000000 / 711268185677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (70488291 / 200000000) (22027591 / 62500000) (Real.log (711268185677 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (711268185677 / 500000000000) = -Real.log (500000000000 / 711268185677) := by
    rw [show ((711268185677 / 500000000000) : ℝ) = ((500000000000 / 711268185677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (88272299 / 250000000) ≤ -Real.log (500000000000 / 711729052537) ∧
    -Real.log (500000000000 / 711729052537) ≤ (353089197 / 1000000000) := by
  have h := checkLog_sound (w := (211729052537 / 1211729052537)) (n := 12)
    (lo := (88272299 / 250000000)) (hi := (353089197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711729052537 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711729052537 / 500000000000) = 1/(500000000000 / 711729052537) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (88272299 / 250000000) (353089197 / 1000000000) (Real.log (711729052537 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (711729052537 / 500000000000) = -Real.log (500000000000 / 711729052537) := by
    rw [show ((711729052537 / 500000000000) : ℝ) = ((500000000000 / 711729052537) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (1550371 / 50000000) ≤ -Real.log (969468378711 / 1000000000000) ∧
    -Real.log (969468378711 / 1000000000000) ≤ (31007421 / 1000000000) := by
  have h := checkLog_sound (w := (30531621289 / 1969468378711)) (n := 12)
    (lo := (1550371 / 50000000)) (hi := (31007421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969468378711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969468378711) = 1/(969468378711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31007421 / 1000000000) (-1550371 / 50000000) (Real.log (969468378711 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1544717 / 50000000) ≤ -Real.log (969578012439 / 1000000000000) ∧
    -Real.log (969578012439 / 1000000000000) ≤ (30894341 / 1000000000) := by
  have h := checkLog_sound (w := (30421987561 / 1969578012439)) (n := 12)
    (lo := (1544717 / 50000000)) (hi := (30894341 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969578012439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969578012439) = 1/(969578012439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-30894341 / 1000000000) (-1544717 / 50000000) (Real.log (969578012439 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell156

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell157Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell157
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

theorem reflection_log_1_neg : (294591739 / 1000000000) ≤ -Real.log (2560 / 3437) ∧
    -Real.log (2560 / 3437) ≤ (14729587 / 50000000) := by
  have h := checkLog_sound (w := (877 / 5997)) (n := 12)
    (lo := (294591739 / 1000000000)) (hi := (14729587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3437 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3437 / 2560) = 1/(2560 / 3437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (294591739 / 1000000000) (14729587 / 50000000) (Real.log (3437 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3437 / 2560) = -Real.log (2560 / 3437) := by
    rw [show ((3437 / 2560) : ℝ) = ((2560 / 3437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (419429343 / 1000000000) ≤ -Real.log (1683 / 2560) ∧
    -Real.log (1683 / 2560) ≤ (13107167 / 31250000) := by
  have h := checkLog_sound (w := (877 / 4243)) (n := 12)
    (lo := (419429343 / 1000000000)) (hi := (13107167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1683) = 1/(1683 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-13107167 / 31250000) (-419429343 / 1000000000) (Real.log (1683 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (18384701 / 62500000) ≤ -Real.log (5120 / 6871) ∧
    -Real.log (5120 / 6871) ≤ (294155217 / 1000000000) := by
  have h := checkLog_sound (w := (1751 / 11991)) (n := 12)
    (lo := (18384701 / 62500000)) (hi := (294155217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6871 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6871 / 5120) = 1/(5120 / 6871) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (18384701 / 62500000) (294155217 / 1000000000) (Real.log (6871 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6871 / 5120) = -Real.log (5120 / 6871) := by
    rw [show ((6871 / 5120) : ℝ) = ((5120 / 6871) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (209269237 / 500000000) ≤ -Real.log (3369 / 5120) ∧
    -Real.log (3369 / 5120) ≤ (16741539 / 40000000) := by
  have h := checkLog_sound (w := (1751 / 8489)) (n := 12)
    (lo := (209269237 / 500000000)) (hi := (16741539 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3369) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3369) = 1/(3369 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-16741539 / 40000000) (-209269237 / 500000000) (Real.log (3369 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (217579299 / 1000000000) ≤ -Real.log (125000 / 155383) ∧
    -Real.log (125000 / 155383) ≤ (2175793 / 10000000) := by
  have h := checkLog_sound (w := (30383 / 280383)) (n := 12)
    (lo := (217579299 / 1000000000)) (hi := (2175793 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155383 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155383 / 125000) = 1/(125000 / 155383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (217579299 / 1000000000) (2175793 / 10000000) (Real.log (155383 / 125000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (155383 / 125000) = -Real.log (125000 / 155383) := by
    rw [show ((155383 / 125000) : ℝ) = ((125000 / 155383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (278476573 / 1000000000) ≤ -Real.log (94617 / 125000) ∧
    -Real.log (94617 / 125000) ≤ (139238287 / 500000000) := by
  have h := checkLog_sound (w := (30383 / 219617)) (n := 12)
    (lo := (278476573 / 1000000000)) (hi := (139238287 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94617) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94617) = 1/(94617 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139238287 / 500000000) (-278476573 / 1000000000) (Real.log (94617 / 125000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (8716749 / 40000000) ≤ -Real.log (500000 / 621743) ∧
    -Real.log (500000 / 621743) ≤ (108959363 / 500000000) := by
  have h := checkLog_sound (w := (121743 / 1121743)) (n := 12)
    (lo := (8716749 / 40000000)) (hi := (108959363 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621743 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621743 / 500000) = 1/(500000 / 621743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (8716749 / 40000000) (108959363 / 500000000) (Real.log (621743 / 500000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (621743 / 500000) = -Real.log (500000 / 621743) := by
    rw [show ((621743 / 500000) : ℝ) = ((500000 / 621743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (279034239 / 1000000000) ≤ -Real.log (378257 / 500000) ∧
    -Real.log (378257 / 500000) ≤ (435991 / 1562500) := by
  have h := checkLog_sound (w := (121743 / 878257)) (n := 12)
    (lo := (279034239 / 1000000000)) (hi := (435991 / 1562500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378257) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378257) = 1/(378257 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-435991 / 1562500) (-279034239 / 1000000000) (Real.log (378257 / 500000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40260009 / 250000000) ≤ -Real.log (250000 / 293683) ∧
    -Real.log (250000 / 293683) ≤ (161040037 / 1000000000) := by
  have h := checkLog_sound (w := (43683 / 543683)) (n := 12)
    (lo := (40260009 / 250000000)) (hi := (161040037 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293683 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(293683 / 250000) = 1/(250000 / 293683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40260009 / 250000000) (161040037 / 1000000000) (Real.log (293683 / 250000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (293683 / 250000) = -Real.log (250000 / 293683) := by
    rw [show ((293683 / 250000) : ℝ) = ((250000 / 293683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (24005887 / 125000000) ≤ -Real.log (206317 / 250000) ∧
    -Real.log (206317 / 250000) ≤ (192047097 / 1000000000) := by
  have h := checkLog_sound (w := (43683 / 456317)) (n := 12)
    (lo := (24005887 / 125000000)) (hi := (192047097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 206317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 206317) = 1/(206317 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-192047097 / 1000000000) (-24005887 / 125000000) (Real.log (206317 / 250000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (32261459 / 200000000) ≤ -Real.log (500000 / 587523) ∧
    -Real.log (500000 / 587523) ≤ (5040853 / 31250000) := by
  have h := checkLog_sound (w := (87523 / 1087523)) (n := 12)
    (lo := (32261459 / 200000000)) (hi := (5040853 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587523 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587523 / 500000) = 1/(500000 / 587523) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (32261459 / 200000000) (5040853 / 31250000) (Real.log (587523 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587523 / 500000) = -Real.log (500000 / 587523) := by
    rw [show ((587523 / 500000) : ℝ) = ((500000 / 587523) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (192427651 / 1000000000) ≤ -Real.log (412477 / 500000) ∧
    -Real.log (412477 / 500000) ≤ (48106913 / 250000000) := by
  have h := checkLog_sound (w := (87523 / 912477)) (n := 12)
    (lo := (192427651 / 1000000000)) (hi := (48106913 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412477) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412477) = 1/(412477 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48106913 / 250000000) (-192427651 / 1000000000) (Real.log (412477 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (712693691 / 1000000000) ≤ -Real.log (250000000000 / 509869397447) ∧
    -Real.log (250000000000 / 509869397447) ≤ (712693693 / 1000000000) := by
  have h := checkLog_sound (w := (9869397447 / 1009869397447)) (n := 12)
    (lo := (19546511 / 1000000000)) (hi := (1221657 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((509869397447 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(509869397447 / 500000000000) = 1/(250000000000 / 509869397447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (712693691 / 1000000000) (712693693 / 1000000000) (Real.log (509869397447 / 250000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (509869397447 / 250000000000) = -Real.log (250000000000 / 509869397447) := by
    rw [show ((509869397447 / 250000000000) : ℝ) = ((250000000000 / 509869397447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (357010541 / 500000000) ≤ -Real.log (2500000000 / 5105466429) ∧
    -Real.log (2500000000 / 5105466429) ≤ (178505271 / 250000000) := by
  have h := checkLog_sound (w := (105466429 / 10105466429)) (n := 12)
    (lo := (10436951 / 500000000)) (hi := (20873903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5105466429 / 5000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(5105466429 / 5000000000) = 1/(2500000000 / 5105466429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (357010541 / 500000000) (178505271 / 250000000) (Real.log (5105466429 / 2500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (5105466429 / 2500000000) = -Real.log (2500000000 / 5105466429) := by
    rw [show ((5105466429 / 2500000000) : ℝ) = ((2500000000 / 5105466429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (7750873 / 15625000) ≤ -Real.log (125000000000 / 205278913937) ∧
    -Real.log (125000000000 / 205278913937) ≤ (496055873 / 1000000000) := by
  have h := checkLog_sound (w := (80278913937 / 330278913937)) (n := 12)
    (lo := (7750873 / 15625000)) (hi := (496055873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205278913937 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(205278913937 / 125000000000) = 1/(125000000000 / 205278913937) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (7750873 / 15625000) (496055873 / 1000000000) (Real.log (205278913937 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (205278913937 / 125000000000) = -Real.log (125000000000 / 205278913937) := by
    rw [show ((205278913937 / 125000000000) : ℝ) = ((125000000000 / 205278913937) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (99390593 / 200000000) ≤ -Real.log (25000000000 / 41092630143) ∧
    -Real.log (25000000000 / 41092630143) ≤ (248476483 / 500000000) := by
  have h := checkLog_sound (w := (16092630143 / 66092630143)) (n := 12)
    (lo := (99390593 / 200000000)) (hi := (248476483 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41092630143 / 25000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(41092630143 / 25000000000) = 1/(25000000000 / 41092630143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (99390593 / 200000000) (248476483 / 500000000) (Real.log (41092630143 / 25000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (41092630143 / 25000000000) = -Real.log (25000000000 / 41092630143) := by
    rw [show ((41092630143 / 25000000000) : ℝ) = ((25000000000 / 41092630143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (353087133 / 1000000000) ≤ -Real.log (500000000000 / 711727584251) ∧
    -Real.log (500000000000 / 711727584251) ≤ (176543567 / 500000000) := by
  have h := checkLog_sound (w := (211727584251 / 1211727584251)) (n := 12)
    (lo := (353087133 / 1000000000)) (hi := (176543567 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((711727584251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(711727584251 / 500000000000) = 1/(500000000000 / 711727584251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (353087133 / 1000000000) (176543567 / 500000000) (Real.log (711727584251 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (711727584251 / 500000000000) = -Real.log (500000000000 / 711727584251) := by
    rw [show ((711727584251 / 500000000000) : ℝ) = ((500000000000 / 711727584251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (353734947 / 1000000000) ≤ -Real.log (500000000000 / 712188800831) ∧
    -Real.log (500000000000 / 712188800831) ≤ (88433737 / 250000000) := by
  have h := checkLog_sound (w := (212188800831 / 1212188800831)) (n := 12)
    (lo := (353734947 / 1000000000)) (hi := (88433737 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712188800831 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712188800831 / 500000000000) = 1/(500000000000 / 712188800831) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (353734947 / 1000000000) (88433737 / 250000000) (Real.log (712188800831 / 500000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (712188800831 / 500000000000) = -Real.log (500000000000 / 712188800831) := by
    rw [show ((712188800831 / 500000000000) : ℝ) = ((500000000000 / 712188800831) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7780089 / 250000000) ≤ -Real.log (242339724471 / 250000000000) ∧
    -Real.log (242339724471 / 250000000000) ≤ (31120357 / 1000000000) := by
  have h := checkLog_sound (w := (7660275529 / 492339724471)) (n := 12)
    (lo := (7780089 / 250000000)) (hi := (31120357 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242339724471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242339724471) = 1/(242339724471 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31120357 / 1000000000) (-7780089 / 250000000) (Real.log (242339724471 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (1550353 / 50000000) ≤ -Real.log (60591795511 / 62500000000) ∧
    -Real.log (60591795511 / 62500000000) ≤ (31007061 / 1000000000) := by
  have h := checkLog_sound (w := (1908204489 / 123091795511)) (n := 12)
    (lo := (1550353 / 50000000)) (hi := (31007061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60591795511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60591795511) = 1/(60591795511 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31007061 / 1000000000) (-1550353 / 50000000) (Real.log (60591795511 / 62500000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell157

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell158Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell158
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

theorem reflection_log_1_neg : (295028071 / 1000000000) ≤ -Real.log (5120 / 6877) ∧
    -Real.log (5120 / 6877) ≤ (36878509 / 125000000) := by
  have h := checkLog_sound (w := (1757 / 11997)) (n := 12)
    (lo := (295028071 / 1000000000)) (hi := (36878509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6877 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6877 / 5120) = 1/(5120 / 6877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (295028071 / 1000000000) (36878509 / 125000000) (Real.log (6877 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6877 / 5120) = -Real.log (5120 / 6877) := by
    rw [show ((6877 / 5120) : ℝ) = ((5120 / 6877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (210160503 / 500000000) ≤ -Real.log (3363 / 5120) ∧
    -Real.log (3363 / 5120) ≤ (420321007 / 1000000000) := by
  have h := checkLog_sound (w := (1757 / 8483)) (n := 12)
    (lo := (210160503 / 500000000)) (hi := (420321007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3363) = 1/(3363 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-420321007 / 1000000000) (-210160503 / 500000000) (Real.log (3363 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (294591739 / 1000000000) ≤ -Real.log (2560 / 3437) ∧
    -Real.log (2560 / 3437) ≤ (14729587 / 50000000) := by
  have h := checkLog_sound (w := (877 / 5997)) (n := 12)
    (lo := (294591739 / 1000000000)) (hi := (14729587 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3437 / 2560) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3437 / 2560) = 1/(2560 / 3437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (294591739 / 1000000000) (14729587 / 50000000) (Real.log (3437 / 2560)) := by
  have h := reflection_log_3_neg
  have he : Real.log (3437 / 2560) = -Real.log (2560 / 3437) := by
    rw [show ((3437 / 2560) : ℝ) = ((2560 / 3437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (419429343 / 1000000000) ≤ -Real.log (1683 / 2560) ∧
    -Real.log (1683 / 2560) ≤ (13107167 / 31250000) := by
  have h := checkLog_sound (w := (877 / 4243)) (n := 12)
    (lo := (419429343 / 1000000000)) (hi := (13107167 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2560 / 1683) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2560 / 1683) = 1/(1683 / 2560) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-13107167 / 31250000) (-419429343 / 1000000000) (Real.log (1683 / 2560)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (217917921 / 1000000000) ≤ -Real.log (200000 / 248697) ∧
    -Real.log (200000 / 248697) ≤ (108958961 / 500000000) := by
  have h := checkLog_sound (w := (48697 / 448697)) (n := 12)
    (lo := (217917921 / 1000000000)) (hi := (108958961 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248697 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248697 / 200000) = 1/(200000 / 248697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (217917921 / 1000000000) (108958961 / 500000000) (Real.log (248697 / 200000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (248697 / 200000) = -Real.log (200000 / 248697) := by
    rw [show ((248697 / 200000) : ℝ) = ((200000 / 248697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279032917 / 1000000000) ≤ -Real.log (151303 / 200000) ∧
    -Real.log (151303 / 200000) ≤ (139516459 / 500000000) := by
  have h := checkLog_sound (w := (48697 / 351303)) (n := 12)
    (lo := (279032917 / 1000000000)) (hi := (139516459 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 151303) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 151303) = 1/(151303 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-139516459 / 500000000) (-279032917 / 1000000000) (Real.log (151303 / 200000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (13641077 / 62500000) ≤ -Real.log (1000000 / 1243907) ∧
    -Real.log (1000000 / 1243907) ≤ (218257233 / 1000000000) := by
  have h := checkLog_sound (w := (243907 / 2243907)) (n := 12)
    (lo := (13641077 / 62500000)) (hi := (218257233 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1243907 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1243907 / 1000000) = 1/(1000000 / 1243907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (13641077 / 62500000) (218257233 / 1000000000) (Real.log (1243907 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1243907 / 1000000) = -Real.log (1000000 / 1243907) := by
    rw [show ((1243907 / 1000000) : ℝ) = ((1000000 / 1243907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (139795447 / 500000000) ≤ -Real.log (756093 / 1000000) ∧
    -Real.log (756093 / 1000000) ≤ (55918179 / 200000000) := by
  have h := checkLog_sound (w := (243907 / 1756093)) (n := 12)
    (lo := (139795447 / 500000000)) (hi := (55918179 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 756093) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 756093) = 1/(756093 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-55918179 / 200000000) (-139795447 / 500000000) (Real.log (756093 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (40326611 / 250000000) ≤ -Real.log (200000 / 235009) ∧
    -Real.log (200000 / 235009) ≤ (32261289 / 200000000) := by
  have h := checkLog_sound (w := (35009 / 435009)) (n := 12)
    (lo := (40326611 / 250000000)) (hi := (32261289 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((235009 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(235009 / 200000) = 1/(200000 / 235009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (40326611 / 250000000) (32261289 / 200000000) (Real.log (235009 / 200000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (235009 / 200000) = -Real.log (200000 / 235009) := by
    rw [show ((235009 / 200000) : ℝ) = ((200000 / 235009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192426439 / 1000000000) ≤ -Real.log (164991 / 200000) ∧
    -Real.log (164991 / 200000) ≤ (4810661 / 25000000) := by
  have h := checkLog_sound (w := (35009 / 364991)) (n := 12)
    (lo := (192426439 / 1000000000)) (hi := (4810661 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 164991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 164991) = 1/(164991 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-4810661 / 25000000) (-192426439 / 1000000000) (Real.log (164991 / 200000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (80786391 / 500000000) ≤ -Real.log (500000 / 587679) ∧
    -Real.log (500000 / 587679) ≤ (161572783 / 1000000000) := by
  have h := checkLog_sound (w := (87679 / 1087679)) (n := 12)
    (lo := (80786391 / 500000000)) (hi := (161572783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((587679 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(587679 / 500000) = 1/(500000 / 587679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (80786391 / 500000000) (161572783 / 1000000000) (Real.log (587679 / 500000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (587679 / 500000) = -Real.log (500000 / 587679) := by
    rw [show ((587679 / 500000) : ℝ) = ((500000 / 587679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (96402963 / 500000000) ≤ -Real.log (412321 / 500000) ∧
    -Real.log (412321 / 500000) ≤ (192805927 / 1000000000) := by
  have h := checkLog_sound (w := (87679 / 912321)) (n := 12)
    (lo := (96402963 / 500000000)) (hi := (192805927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 412321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 412321) = 1/(412321 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-192805927 / 1000000000) (-96402963 / 500000000) (Real.log (412321 / 500000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (357010541 / 500000000) ≤ -Real.log (500000000000 / 1021093285799) ∧
    -Real.log (500000000000 / 1021093285799) ≤ (178505271 / 250000000) := by
  have h := checkLog_sound (w := (21093285799 / 2021093285799)) (n := 12)
    (lo := (10436951 / 500000000)) (hi := (20873903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1021093285799 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1021093285799 / 1000000000000) = 1/(500000000000 / 1021093285799) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (357010541 / 500000000) (178505271 / 250000000) (Real.log (1021093285799 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1021093285799 / 500000000000) = -Real.log (500000000000 / 1021093285799) := by
    rw [show ((1021093285799 / 500000000000) : ℝ) = ((500000000000 / 1021093285799) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (715349077 / 1000000000) ≤ -Real.log (781250000 / 1597578427) ∧
    -Real.log (781250000 / 1597578427) ≤ (715349079 / 1000000000) := by
  have h := checkLog_sound (w := (35078427 / 3160078427)) (n := 12)
    (lo := (22201897 / 1000000000)) (hi := (11100949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1597578427 / 1562500000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1597578427 / 1562500000) = 1/(781250000 / 1597578427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (715349077 / 1000000000) (715349079 / 1000000000) (Real.log (1597578427 / 781250000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (1597578427 / 781250000) = -Real.log (781250000 / 1597578427) := by
    rw [show ((1597578427 / 781250000) : ℝ) = ((781250000 / 1597578427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (496950839 / 1000000000) ≤ -Real.log (500000000000 / 821850855567) ∧
    -Real.log (500000000000 / 821850855567) ≤ (12423771 / 25000000) := by
  have h := checkLog_sound (w := (321850855567 / 1321850855567)) (n := 12)
    (lo := (496950839 / 1000000000)) (hi := (12423771 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((821850855567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(821850855567 / 500000000000) = 1/(500000000000 / 821850855567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (496950839 / 1000000000) (12423771 / 25000000) (Real.log (821850855567 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (821850855567 / 500000000000) = -Real.log (500000000000 / 821850855567) := by
    rw [show ((821850855567 / 500000000000) : ℝ) = ((500000000000 / 821850855567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (497848127 / 1000000000) ≤ -Real.log (250000000000 / 411294311679) ∧
    -Real.log (250000000000 / 411294311679) ≤ (7778877 / 15625000) := by
  have h := checkLog_sound (w := (161294311679 / 661294311679)) (n := 12)
    (lo := (497848127 / 1000000000)) (hi := (7778877 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411294311679 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411294311679 / 250000000000) = 1/(250000000000 / 411294311679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (497848127 / 1000000000) (7778877 / 15625000) (Real.log (411294311679 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (411294311679 / 250000000000) = -Real.log (250000000000 / 411294311679) := by
    rw [show ((411294311679 / 250000000000) : ℝ) = ((250000000000 / 411294311679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (88433221 / 250000000) ≤ -Real.log (50000000000 / 71218733143) ∧
    -Real.log (50000000000 / 71218733143) ≤ (70746577 / 200000000) := by
  have h := checkLog_sound (w := (21218733143 / 121218733143)) (n := 12)
    (lo := (88433221 / 250000000)) (hi := (70746577 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71218733143 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71218733143 / 50000000000) = 1/(50000000000 / 71218733143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (88433221 / 250000000) (70746577 / 200000000) (Real.log (71218733143 / 50000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (71218733143 / 50000000000) = -Real.log (50000000000 / 71218733143) := by
    rw [show ((71218733143 / 50000000000) : ℝ) = ((50000000000 / 71218733143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (88594677 / 250000000) ≤ -Real.log (125000000000 / 178161856903) ∧
    -Real.log (125000000000 / 178161856903) ≤ (354378709 / 1000000000) := by
  have h := checkLog_sound (w := (53161856903 / 303161856903)) (n := 12)
    (lo := (88594677 / 250000000)) (hi := (354378709 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178161856903 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(178161856903 / 125000000000) = 1/(125000000000 / 178161856903) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (88594677 / 250000000) (354378709 / 1000000000) (Real.log (178161856903 / 125000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (178161856903 / 125000000000) = -Real.log (125000000000 / 178161856903) := by
    rw [show ((178161856903 / 125000000000) : ℝ) = ((125000000000 / 178161856903) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (3904143 / 125000000) ≤ -Real.log (242312392959 / 250000000000) ∧
    -Real.log (242312392959 / 250000000000) ≤ (6246629 / 200000000) := by
  have h := checkLog_sound (w := (7687607041 / 492312392959)) (n := 12)
    (lo := (3904143 / 125000000)) (hi := (6246629 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242312392959) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242312392959) = 1/(242312392959 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-6246629 / 200000000) (-3904143 / 125000000) (Real.log (242312392959 / 250000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15559997 / 500000000) ≤ -Real.log (38774369919 / 40000000000) ∧
    -Real.log (38774369919 / 40000000000) ≤ (6223999 / 200000000) := by
  have h := checkLog_sound (w := (1225630081 / 78774369919)) (n := 12)
    (lo := (15559997 / 500000000)) (hi := (6223999 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38774369919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38774369919) = 1/(38774369919 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-6223999 / 200000000) (-15559997 / 500000000) (Real.log (38774369919 / 40000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell158

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell159Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell159
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

theorem reflection_log_1_neg : (73866053 / 250000000) ≤ -Real.log (32 / 43) ∧
    -Real.log (32 / 43) ≤ (295464213 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 75)) (n := 12)
    (lo := (73866053 / 250000000)) (hi := (295464213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 32) = 1/(32 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73866053 / 250000000) (295464213 / 1000000000) (Real.log (43 / 32)) := by
  have h := reflection_log_1_neg
  have he : Real.log (43 / 32) = -Real.log (32 / 43) := by
    rw [show ((43 / 32) : ℝ) = ((32 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (84242693 / 200000000) ≤ -Real.log (21 / 32) ∧
    -Real.log (21 / 32) ≤ (210606733 / 500000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 21) = 1/(21 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-210606733 / 500000000) (-84242693 / 200000000) (Real.log (21 / 32)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (295028071 / 1000000000) ≤ -Real.log (5120 / 6877) ∧
    -Real.log (5120 / 6877) ≤ (36878509 / 125000000) := by
  have h := checkLog_sound (w := (1757 / 11997)) (n := 12)
    (lo := (295028071 / 1000000000)) (hi := (36878509 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6877 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6877 / 5120) = 1/(5120 / 6877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (295028071 / 1000000000) (36878509 / 125000000) (Real.log (6877 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6877 / 5120) = -Real.log (5120 / 6877) := by
    rw [show ((6877 / 5120) : ℝ) = ((5120 / 6877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (210160503 / 500000000) ≤ -Real.log (3363 / 5120) ∧
    -Real.log (3363 / 5120) ≤ (420321007 / 1000000000) := by
  have h := checkLog_sound (w := (1757 / 8483)) (n := 12)
    (lo := (210160503 / 500000000)) (hi := (420321007 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3363) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3363) = 1/(3363 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-420321007 / 1000000000) (-210160503 / 500000000) (Real.log (3363 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (54564107 / 250000000) ≤ -Real.log (500000 / 621953) ∧
    -Real.log (500000 / 621953) ≤ (218256429 / 1000000000) := by
  have h := checkLog_sound (w := (121953 / 1121953)) (n := 12)
    (lo := (54564107 / 250000000)) (hi := (218256429 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((621953 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(621953 / 500000) = 1/(500000 / 621953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (54564107 / 250000000) (218256429 / 1000000000) (Real.log (621953 / 500000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (621953 / 500000) = -Real.log (500000 / 621953) := by
    rw [show ((621953 / 500000) : ℝ) = ((500000 / 621953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (279589571 / 1000000000) ≤ -Real.log (378047 / 500000) ∧
    -Real.log (378047 / 500000) ≤ (69897393 / 250000000) := by
  have h := checkLog_sound (w := (121953 / 878047)) (n := 12)
    (lo := (279589571 / 1000000000)) (hi := (69897393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 378047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 378047) = 1/(378047 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-69897393 / 250000000) (-279589571 / 1000000000) (Real.log (378047 / 500000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (349753 / 1600000) ≤ -Real.log (125000 / 155541) ∧
    -Real.log (125000 / 155541) ≤ (109297813 / 500000000) := by
  have h := checkLog_sound (w := (30541 / 280541)) (n := 12)
    (lo := (349753 / 1600000)) (hi := (109297813 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155541 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155541 / 125000) = 1/(125000 / 155541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (349753 / 1600000) (109297813 / 500000000) (Real.log (155541 / 125000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (155541 / 125000) = -Real.log (125000 / 155541) := by
    rw [show ((155541 / 125000) : ℝ) = ((125000 / 155541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (280147859 / 1000000000) ≤ -Real.log (94459 / 125000) ∧
    -Real.log (94459 / 125000) ≤ (14007393 / 50000000) := by
  have h := checkLog_sound (w := (30541 / 219459)) (n := 12)
    (lo := (280147859 / 1000000000)) (hi := (14007393 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 94459) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 94459) = 1/(94459 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-14007393 / 50000000) (-280147859 / 1000000000) (Real.log (94459 / 125000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161571931 / 1000000000) ≤ -Real.log (1000000 / 1175357) ∧
    -Real.log (1000000 / 1175357) ≤ (40392983 / 250000000) := by
  have h := checkLog_sound (w := (175357 / 2175357)) (n := 12)
    (lo := (161571931 / 1000000000)) (hi := (40392983 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175357 / 1000000) = 1/(1000000 / 1175357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161571931 / 1000000000) (40392983 / 250000000) (Real.log (1175357 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1175357 / 1000000) = -Real.log (1000000 / 1175357) := by
    rw [show ((1175357 / 1000000) : ℝ) = ((1000000 / 1175357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (192804713 / 1000000000) ≤ -Real.log (824643 / 1000000) ∧
    -Real.log (824643 / 1000000) ≤ (96402357 / 500000000) := by
  have h := checkLog_sound (w := (175357 / 1824643)) (n := 12)
    (lo := (192804713 / 1000000000)) (hi := (96402357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824643) = 1/(824643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-96402357 / 500000000) (-192804713 / 1000000000) (Real.log (824643 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20229881 / 125000000) ≤ -Real.log (1000000 / 1175671) ∧
    -Real.log (1000000 / 1175671) ≤ (161839049 / 1000000000) := by
  have h := checkLog_sound (w := (175671 / 2175671)) (n := 12)
    (lo := (20229881 / 125000000)) (hi := (161839049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175671 / 1000000) = 1/(1000000 / 1175671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20229881 / 125000000) (161839049 / 1000000000) (Real.log (1175671 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1175671 / 1000000) = -Real.log (1000000 / 1175671) := by
    rw [show ((1175671 / 1000000) : ℝ) = ((1000000 / 1175671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (48296389 / 250000000) ≤ -Real.log (824329 / 1000000) ∧
    -Real.log (824329 / 1000000) ≤ (193185557 / 1000000000) := by
  have h := checkLog_sound (w := (175671 / 1824329)) (n := 12)
    (lo := (48296389 / 250000000)) (hi := (193185557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824329) = 1/(824329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193185557 / 1000000000) (-48296389 / 250000000) (Real.log (824329 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (715349077 / 1000000000) ≤ -Real.log (500000000000 / 1022450193279) ∧
    -Real.log (500000000000 / 1022450193279) ≤ (715349079 / 1000000000) := by
  have h := checkLog_sound (w := (22450193279 / 2022450193279)) (n := 12)
    (lo := (22201897 / 1000000000)) (hi := (11100949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1022450193279 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1022450193279 / 1000000000000) = 1/(500000000000 / 1022450193279) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (715349077 / 1000000000) (715349079 / 1000000000) (Real.log (1022450193279 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1022450193279 / 500000000000) = -Real.log (500000000000 / 1022450193279) := by
    rw [show ((1022450193279 / 500000000000) : ℝ) = ((500000000000 / 1022450193279) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (716677677 / 1000000000) ≤ -Real.log (50000000000 / 102380952381) ∧
    -Real.log (50000000000 / 102380952381) ≤ (716677679 / 1000000000) := by
  have h := checkLog_sound (w := (2380952381 / 202380952381)) (n := 12)
    (lo := (23530497 / 1000000000)) (hi := (11765249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((102380952381 / 100000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(102380952381 / 100000000000) = 1/(50000000000 / 102380952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (716677677 / 1000000000) (716677679 / 1000000000) (Real.log (102380952381 / 50000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (102380952381 / 50000000000) = -Real.log (50000000000 / 102380952381) := by
    rw [show ((102380952381 / 50000000000) : ℝ) = ((50000000000 / 102380952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (248923 / 500000) ≤ -Real.log (250000000000 / 411293437059) ∧
    -Real.log (250000000000 / 411293437059) ≤ (497846001 / 1000000000) := by
  have h := checkLog_sound (w := (161293437059 / 661293437059)) (n := 12)
    (lo := (248923 / 500000)) (hi := (497846001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411293437059 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411293437059 / 250000000000) = 1/(250000000000 / 411293437059) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (248923 / 500000) (497846001 / 1000000000) (Real.log (411293437059 / 250000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (411293437059 / 250000000000) = -Real.log (250000000000 / 411293437059) := by
    rw [show ((411293437059 / 250000000000) : ℝ) = ((250000000000 / 411293437059) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (124685871 / 250000000) ≤ -Real.log (250000000000 / 411662731979) ∧
    -Real.log (250000000000 / 411662731979) ≤ (99748697 / 200000000) := by
  have h := checkLog_sound (w := (161662731979 / 661662731979)) (n := 12)
    (lo := (124685871 / 250000000)) (hi := (99748697 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((411662731979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(411662731979 / 250000000000) = 1/(250000000000 / 411662731979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (124685871 / 250000000) (99748697 / 200000000) (Real.log (411662731979 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (411662731979 / 250000000000) = -Real.log (250000000000 / 411662731979) := by
    rw [show ((411662731979 / 250000000000) : ℝ) = ((250000000000 / 411662731979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (88594161 / 250000000) ≤ -Real.log (500000000000 / 712645957099) ∧
    -Real.log (500000000000 / 712645957099) ≤ (70875329 / 200000000) := by
  have h := checkLog_sound (w := (212645957099 / 1212645957099)) (n := 12)
    (lo := (88594161 / 250000000)) (hi := (70875329 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((712645957099 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(712645957099 / 500000000000) = 1/(500000000000 / 712645957099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (88594161 / 250000000) (70875329 / 200000000) (Real.log (712645957099 / 500000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (712645957099 / 500000000000) = -Real.log (500000000000 / 712645957099) := by
    rw [show ((712645957099 / 500000000000) : ℝ) = ((500000000000 / 712645957099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (71004921 / 200000000) ≤ -Real.log (62500000000 / 89138484149) ∧
    -Real.log (62500000000 / 89138484149) ≤ (177512303 / 500000000) := by
  have h := checkLog_sound (w := (26638484149 / 151638484149)) (n := 12)
    (lo := (71004921 / 200000000)) (hi := (177512303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89138484149 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89138484149 / 62500000000) = 1/(62500000000 / 89138484149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (71004921 / 200000000) (177512303 / 500000000) (Real.log (89138484149 / 62500000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (89138484149 / 62500000000) = -Real.log (62500000000 / 89138484149) := by
    rw [show ((89138484149 / 62500000000) : ℝ) = ((62500000000 / 89138484149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (7836627 / 250000000) ≤ -Real.log (969139699759 / 1000000000000) ∧
    -Real.log (969139699759 / 1000000000000) ≤ (31346509 / 1000000000) := by
  have h := checkLog_sound (w := (30860300241 / 1969139699759)) (n := 12)
    (lo := (7836627 / 250000000)) (hi := (31346509 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969139699759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969139699759) = 1/(969139699759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31346509 / 1000000000) (-7836627 / 250000000) (Real.log (969139699759 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (15616391 / 500000000) ≤ -Real.log (969249922551 / 1000000000000) ∧
    -Real.log (969249922551 / 1000000000000) ≤ (31232783 / 1000000000) := by
  have h := checkLog_sound (w := (30750077449 / 1969249922551)) (n := 12)
    (lo := (15616391 / 500000000)) (hi := (31232783 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969249922551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969249922551) = 1/(969249922551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-31232783 / 1000000000) (-15616391 / 500000000) (Real.log (969249922551 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell159

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell160Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell160
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

theorem reflection_log_1_neg : (73975041 / 250000000) ≤ -Real.log (5120 / 6883) ∧
    -Real.log (5120 / 6883) ≤ (59180033 / 200000000) := by
  have h := checkLog_sound (w := (1763 / 12003)) (n := 12)
    (lo := (73975041 / 250000000)) (hi := (59180033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6883 / 5120) = 1/(5120 / 6883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1 : Bounds (73975041 / 250000000) (59180033 / 200000000) (Real.log (6883 / 5120)) := by
  have h := reflection_log_1_neg
  have he : Real.log (6883 / 5120) = -Real.log (5120 / 6883) := by
    rw [show ((6883 / 5120) : ℝ) = ((5120 / 6883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (422106721 / 1000000000) ≤ -Real.log (3357 / 5120) ∧
    -Real.log (3357 / 5120) ≤ (211053361 / 500000000) := by
  have h := checkLog_sound (w := (1763 / 8477)) (n := 12)
    (lo := (422106721 / 1000000000)) (hi := (211053361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3357) = 1/(3357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_2 : Bounds (-211053361 / 500000000) (-422106721 / 1000000000) (Real.log (3357 / 5120)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73866053 / 250000000) ≤ -Real.log (32 / 43) ∧
    -Real.log (32 / 43) ≤ (295464213 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 75)) (n := 12)
    (lo := (73866053 / 250000000)) (hi := (295464213 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((43 / 32) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(43 / 32) = 1/(32 / 43) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73866053 / 250000000) (295464213 / 1000000000) (Real.log (43 / 32)) := by
  have h := reflection_log_3_neg
  have he : Real.log (43 / 32) = -Real.log (32 / 43) := by
    rw [show ((43 / 32) : ℝ) = ((32 / 43) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (84242693 / 200000000) ≤ -Real.log (21 / 32) ∧
    -Real.log (21 / 32) ≤ (210606733 / 500000000) := by
  have h := checkLog_sound (w := (11 / 53)) (n := 12)
    (lo := (84242693 / 200000000)) (hi := (210606733 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((32 / 21) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(32 / 21) = 1/(21 / 32) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-210606733 / 500000000) (-84242693 / 200000000) (Real.log (21 / 32)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (218594821 / 1000000000) ≤ -Real.log (1000000 / 1244327) ∧
    -Real.log (1000000 / 1244327) ≤ (109297411 / 500000000) := by
  have h := checkLog_sound (w := (244327 / 2244327)) (n := 12)
    (lo := (218594821 / 1000000000)) (hi := (109297411 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244327 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244327 / 1000000) = 1/(1000000 / 1244327) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (218594821 / 1000000000) (109297411 / 500000000) (Real.log (1244327 / 1000000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (1244327 / 1000000) = -Real.log (1000000 / 1244327) := by
    rw [show ((1244327 / 1000000) : ℝ) = ((1000000 / 1244327) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (35018317 / 125000000) ≤ -Real.log (755673 / 1000000) ∧
    -Real.log (755673 / 1000000) ≤ (280146537 / 1000000000) := by
  have h := checkLog_sound (w := (244327 / 1755673)) (n := 12)
    (lo := (35018317 / 125000000)) (hi := (280146537 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755673) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755673) = 1/(755673 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280146537 / 1000000000) (-35018317 / 125000000) (Real.log (755673 / 1000000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (218933903 / 1000000000) ≤ -Real.log (1000000 / 1244749) ∧
    -Real.log (1000000 / 1244749) ≤ (13683369 / 62500000) := by
  have h := checkLog_sound (w := (244749 / 2244749)) (n := 12)
    (lo := (218933903 / 1000000000)) (hi := (13683369 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244749 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244749 / 1000000) = 1/(1000000 / 1244749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (218933903 / 1000000000) (13683369 / 62500000) (Real.log (1244749 / 1000000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (1244749 / 1000000) = -Real.log (1000000 / 1244749) := by
    rw [show ((1244749 / 1000000) : ℝ) = ((1000000 / 1244749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (140352567 / 500000000) ≤ -Real.log (755251 / 1000000) ∧
    -Real.log (755251 / 1000000) ≤ (56141027 / 200000000) := by
  have h := checkLog_sound (w := (244749 / 1755251)) (n := 12)
    (lo := (140352567 / 500000000)) (hi := (56141027 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 755251) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 755251) = 1/(755251 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-56141027 / 200000000) (-140352567 / 500000000) (Real.log (755251 / 1000000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (161838197 / 1000000000) ≤ -Real.log (100000 / 117567) ∧
    -Real.log (100000 / 117567) ≤ (80919099 / 500000000) := by
  have h := checkLog_sound (w := (17567 / 217567)) (n := 12)
    (lo := (161838197 / 1000000000)) (hi := (80919099 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117567 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117567 / 100000) = 1/(100000 / 117567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (161838197 / 1000000000) (80919099 / 500000000) (Real.log (117567 / 100000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (117567 / 100000) = -Real.log (100000 / 117567) := by
    rw [show ((117567 / 100000) : ℝ) = ((100000 / 117567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (193184343 / 1000000000) ≤ -Real.log (82433 / 100000) ∧
    -Real.log (82433 / 100000) ≤ (24148043 / 125000000) := by
  have h := checkLog_sound (w := (17567 / 182433)) (n := 12)
    (lo := (193184343 / 1000000000)) (hi := (24148043 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 82433) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 82433) = 1/(82433 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-24148043 / 125000000) (-193184343 / 1000000000) (Real.log (82433 / 100000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (162105243 / 1000000000) ≤ -Real.log (62500 / 73499) ∧
    -Real.log (62500 / 73499) ≤ (40526311 / 250000000) := by
  have h := checkLog_sound (w := (10999 / 135999)) (n := 12)
    (lo := (162105243 / 1000000000)) (hi := (40526311 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73499 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73499 / 62500) = 1/(62500 / 73499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (162105243 / 1000000000) (40526311 / 250000000) (Real.log (73499 / 62500)) := by
  have h := reflection_log_11_neg
  have he : Real.log (73499 / 62500) = -Real.log (62500 / 73499) := by
    rw [show ((73499 / 62500) : ℝ) = ((62500 / 73499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (193565331 / 1000000000) ≤ -Real.log (51501 / 62500) ∧
    -Real.log (51501 / 62500) ≤ (48391333 / 250000000) := by
  have h := checkLog_sound (w := (10999 / 114001)) (n := 12)
    (lo := (193565331 / 1000000000)) (hi := (48391333 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51501) = 1/(51501 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-48391333 / 250000000) (-193565331 / 1000000000) (Real.log (51501 / 62500)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (716677677 / 1000000000) ≤ -Real.log (500000000000 / 1023809523809) ∧
    -Real.log (500000000000 / 1023809523809) ≤ (716677679 / 1000000000) := by
  have h := checkLog_sound (w := (23809523809 / 2023809523809)) (n := 12)
    (lo := (23530497 / 1000000000)) (hi := (11765249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1023809523809 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1023809523809 / 1000000000000) = 1/(500000000000 / 1023809523809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (716677677 / 1000000000) (716677679 / 1000000000) (Real.log (1023809523809 / 500000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (1023809523809 / 500000000000) = -Real.log (500000000000 / 1023809523809) := by
    rw [show ((1023809523809 / 500000000000) : ℝ) = ((500000000000 / 1023809523809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (179501721 / 250000000) ≤ -Real.log (100000000000 / 205034256777) ∧
    -Real.log (100000000000 / 205034256777) ≤ (359003443 / 500000000) := by
  have h := checkLog_sound (w := (5034256777 / 405034256777)) (n := 12)
    (lo := (3107463 / 125000000)) (hi := (4971941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((205034256777 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(205034256777 / 200000000000) = 1/(100000000000 / 205034256777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (179501721 / 250000000) (359003443 / 500000000) (Real.log (205034256777 / 100000000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (205034256777 / 100000000000) = -Real.log (100000000000 / 205034256777) := by
    rw [show ((205034256777 / 100000000000) : ℝ) = ((100000000000 / 205034256777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (498741357 / 1000000000) ≤ -Real.log (500000000000 / 823323712769) ∧
    -Real.log (500000000000 / 823323712769) ≤ (249370679 / 500000000) := by
  have h := checkLog_sound (w := (323323712769 / 1323323712769)) (n := 12)
    (lo := (498741357 / 1000000000)) (hi := (249370679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((823323712769 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(823323712769 / 500000000000) = 1/(500000000000 / 823323712769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (498741357 / 1000000000) (249370679 / 500000000) (Real.log (823323712769 / 500000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (823323712769 / 500000000000) = -Real.log (500000000000 / 823323712769) := by
    rw [show ((823323712769 / 500000000000) : ℝ) = ((500000000000 / 823323712769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (499639037 / 1000000000) ≤ -Real.log (250000000000 / 412031563017) ∧
    -Real.log (250000000000 / 412031563017) ≤ (249819519 / 500000000) := by
  have h := checkLog_sound (w := (162031563017 / 662031563017)) (n := 12)
    (lo := (499639037 / 1000000000)) (hi := (249819519 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412031563017 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412031563017 / 250000000000) = 1/(250000000000 / 412031563017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (499639037 / 1000000000) (249819519 / 500000000) (Real.log (412031563017 / 250000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (412031563017 / 250000000000) = -Real.log (250000000000 / 412031563017) := by
    rw [show ((412031563017 / 250000000000) : ℝ) = ((250000000000 / 412031563017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (355022541 / 1000000000) ≤ -Real.log (250000000000 / 356553200781) ∧
    -Real.log (250000000000 / 356553200781) ≤ (177511271 / 500000000) := by
  have h := checkLog_sound (w := (106553200781 / 606553200781)) (n := 12)
    (lo := (355022541 / 1000000000)) (hi := (177511271 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356553200781 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356553200781 / 250000000000) = 1/(250000000000 / 356553200781) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355022541 / 1000000000) (177511271 / 500000000) (Real.log (356553200781 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356553200781 / 250000000000) = -Real.log (250000000000 / 356553200781) := by
    rw [show ((356553200781 / 250000000000) : ℝ) = ((250000000000 / 356553200781) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (14226823 / 40000000) ≤ -Real.log (50000000000 / 71356866857) ∧
    -Real.log (50000000000 / 71356866857) ≤ (22229411 / 62500000) := by
  have h := checkLog_sound (w := (21356866857 / 121356866857)) (n := 12)
    (lo := (14226823 / 40000000)) (hi := (22229411 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71356866857 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71356866857 / 50000000000) = 1/(50000000000 / 71356866857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (14226823 / 40000000) (22229411 / 62500000) (Real.log (71356866857 / 50000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (71356866857 / 50000000000) = -Real.log (50000000000 / 71356866857) := by
    rw [show ((71356866857 / 50000000000) : ℝ) = ((50000000000 / 71356866857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (31460087 / 1000000000) ≤ -Real.log (3785271999 / 3906250000) ∧
    -Real.log (3785271999 / 3906250000) ≤ (3932511 / 125000000) := by
  have h := checkLog_sound (w := (120978001 / 7691521999)) (n := 12)
    (lo := (31460087 / 1000000000)) (hi := (3932511 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3785271999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3785271999) = 1/(3785271999 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-3932511 / 125000000) (-31460087 / 1000000000) (Real.log (3785271999 / 3906250000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (6269229 / 200000000) ≤ -Real.log (9691400511 / 10000000000) ∧
    -Real.log (9691400511 / 10000000000) ≤ (15673073 / 500000000) := by
  have h := checkLog_sound (w := (308599489 / 19691400511)) (n := 12)
    (lo := (6269229 / 200000000)) (hi := (15673073 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9691400511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9691400511) = 1/(9691400511 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-15673073 / 500000000) (-6269229 / 200000000) (Real.log (9691400511 / 10000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell160

end

-- ===== source module GeneralCK.Certificates.Generated.DoubleCapHighMiddleDerivative.Cell161Logs =====
section
namespace GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell161
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

theorem reflection_log_1_neg : (11853437 / 40000000) ≤ -Real.log (2560 / 3443) ∧
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


theorem reflection_log_1 : Bounds (11853437 / 40000000) (148167963 / 500000000) (Real.log (3443 / 2560)) := by
  have h := reflection_log_1_neg
  have he : Real.log (3443 / 2560) = -Real.log (2560 / 3443) := by
    rw [show ((3443 / 2560) : ℝ) = ((2560 / 3443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_2_neg : (16920031 / 40000000) ≤ -Real.log (1677 / 2560) ∧
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


theorem reflection_log_2 : Bounds (-52875097 / 125000000) (-16920031 / 40000000) (Real.log (1677 / 2560)) := by
  have h := reflection_log_2_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3_neg : (73975041 / 250000000) ≤ -Real.log (5120 / 6883) ∧
    -Real.log (5120 / 6883) ≤ (59180033 / 200000000) := by
  have h := checkLog_sound (w := (1763 / 12003)) (n := 12)
    (lo := (73975041 / 250000000)) (hi := (59180033 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6883 / 5120) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(6883 / 5120) = 1/(5120 / 6883) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3 : Bounds (73975041 / 250000000) (59180033 / 200000000) (Real.log (6883 / 5120)) := by
  have h := reflection_log_3_neg
  have he : Real.log (6883 / 5120) = -Real.log (5120 / 6883) := by
    rw [show ((6883 / 5120) : ℝ) = ((5120 / 6883) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_4_neg : (422106721 / 1000000000) ≤ -Real.log (3357 / 5120) ∧
    -Real.log (3357 / 5120) ≤ (211053361 / 500000000) := by
  have h := checkLog_sound (w := (1763 / 8477)) (n := 12)
    (lo := (422106721 / 1000000000)) (hi := (211053361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5120 / 3357) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5120 / 3357) = 1/(3357 / 5120) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_4 : Bounds (-211053361 / 500000000) (-422106721 / 1000000000) (Real.log (3357 / 5120)) := by
  have h := reflection_log_4_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_5_neg : (218933099 / 1000000000) ≤ -Real.log (250000 / 311187) ∧
    -Real.log (250000 / 311187) ≤ (2189331 / 10000000) := by
  have h := checkLog_sound (w := (61187 / 561187)) (n := 12)
    (lo := (218933099 / 1000000000)) (hi := (2189331 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((311187 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(311187 / 250000) = 1/(250000 / 311187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_5 : Bounds (218933099 / 1000000000) (2189331 / 10000000) (Real.log (311187 / 250000)) := by
  have h := reflection_log_5_neg
  have he : Real.log (311187 / 250000) = -Real.log (250000 / 311187) := by
    rw [show ((311187 / 250000) : ℝ) = ((250000 / 311187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_6_neg : (28070381 / 100000000) ≤ -Real.log (188813 / 250000) ∧
    -Real.log (188813 / 250000) ≤ (280703811 / 1000000000) := by
  have h := checkLog_sound (w := (61187 / 438813)) (n := 12)
    (lo := (28070381 / 100000000)) (hi := (280703811 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 188813) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 188813) = 1/(188813 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_6 : Bounds (-280703811 / 1000000000) (-28070381 / 100000000) (Real.log (188813 / 250000)) := by
  have h := reflection_log_6_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7_neg : (109636033 / 500000000) ≤ -Real.log (100000 / 124517) ∧
    -Real.log (100000 / 124517) ≤ (219272067 / 1000000000) := by
  have h := checkLog_sound (w := (24517 / 224517)) (n := 12)
    (lo := (109636033 / 500000000)) (hi := (219272067 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((124517 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(124517 / 100000) = 1/(100000 / 124517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7 : Bounds (109636033 / 500000000) (219272067 / 1000000000) (Real.log (124517 / 100000)) := by
  have h := reflection_log_7_neg
  have he : Real.log (124517 / 100000) = -Real.log (100000 / 124517) := by
    rw [show ((124517 / 100000) : ℝ) = ((100000 / 124517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_8_neg : (439473 / 1562500) ≤ -Real.log (75483 / 100000) ∧
    -Real.log (75483 / 100000) ≤ (281262721 / 1000000000) := by
  have h := checkLog_sound (w := (24517 / 175483)) (n := 12)
    (lo := (439473 / 1562500)) (hi := (281262721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 75483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 75483) = 1/(75483 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_8 : Bounds (-281262721 / 1000000000) (-439473 / 1562500) (Real.log (75483 / 100000)) := by
  have h := reflection_log_8_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_9_neg : (162104393 / 1000000000) ≤ -Real.log (1000000 / 1175983) ∧
    -Real.log (1000000 / 1175983) ≤ (81052197 / 500000000) := by
  have h := checkLog_sound (w := (175983 / 2175983)) (n := 12)
    (lo := (162104393 / 1000000000)) (hi := (81052197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1175983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1175983 / 1000000) = 1/(1000000 / 1175983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_9 : Bounds (162104393 / 1000000000) (81052197 / 500000000) (Real.log (1175983 / 1000000)) := by
  have h := reflection_log_9_neg
  have he : Real.log (1175983 / 1000000) = -Real.log (1000000 / 1175983) := by
    rw [show ((1175983 / 1000000) : ℝ) = ((1000000 / 1175983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10_neg : (96782059 / 500000000) ≤ -Real.log (824017 / 1000000) ∧
    -Real.log (824017 / 1000000) ≤ (193564119 / 1000000000) := by
  have h := checkLog_sound (w := (175983 / 1824017)) (n := 12)
    (lo := (96782059 / 500000000)) (hi := (193564119 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 824017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 824017) = 1/(824017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10 : Bounds (-193564119 / 1000000000) (-96782059 / 500000000) (Real.log (824017 / 1000000)) := by
  have h := reflection_log_10_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_11_neg : (20296421 / 125000000) ≤ -Real.log (1000000 / 1176297) ∧
    -Real.log (1000000 / 1176297) ≤ (162371369 / 1000000000) := by
  have h := checkLog_sound (w := (176297 / 2176297)) (n := 12)
    (lo := (20296421 / 125000000)) (hi := (162371369 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1176297 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1176297 / 1000000) = 1/(1000000 / 1176297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_11 : Bounds (20296421 / 125000000) (162371369 / 1000000000) (Real.log (1176297 / 1000000)) := by
  have h := reflection_log_11_neg
  have he : Real.log (1176297 / 1000000) = -Real.log (1000000 / 1176297) := by
    rw [show ((1176297 / 1000000) : ℝ) = ((1000000 / 1176297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_12_neg : (775781 / 4000000) ≤ -Real.log (823703 / 1000000) ∧
    -Real.log (823703 / 1000000) ≤ (193945251 / 1000000000) := by
  have h := checkLog_sound (w := (176297 / 1823703)) (n := 12)
    (lo := (775781 / 4000000)) (hi := (193945251 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 823703) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 823703) = 1/(823703 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_12 : Bounds (-193945251 / 1000000000) (-775781 / 4000000) (Real.log (823703 / 1000000)) := by
  have h := reflection_log_12_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_13_neg : (179501721 / 250000000) ≤ -Real.log (125000000000 / 256292820971) ∧
    -Real.log (125000000000 / 256292820971) ≤ (359003443 / 500000000) := by
  have h := checkLog_sound (w := (6292820971 / 506292820971)) (n := 12)
    (lo := (3107463 / 125000000)) (hi := (4971941 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((256292820971 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(256292820971 / 250000000000) = 1/(125000000000 / 256292820971) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_13 : Bounds (179501721 / 250000000) (359003443 / 500000000) (Real.log (256292820971 / 125000000000)) := by
  have h := reflection_log_13_neg
  have he : Real.log (256292820971 / 125000000000) = -Real.log (125000000000 / 256292820971) := by
    rw [show ((256292820971 / 125000000000) : ℝ) = ((125000000000 / 256292820971) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_14_neg : (7193367 / 10000000) ≤ -Real.log (62500000000 / 128316935003) ∧
    -Real.log (62500000000 / 128316935003) ≤ (359668351 / 500000000) := by
  have h := checkLog_sound (w := (3316935003 / 253316935003)) (n := 12)
    (lo := (327369 / 12500000)) (hi := (26189521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((128316935003 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(128316935003 / 125000000000) = 1/(62500000000 / 128316935003) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_14 : Bounds (7193367 / 10000000) (359668351 / 500000000) (Real.log (128316935003 / 62500000000)) := by
  have h := reflection_log_14_neg
  have he : Real.log (128316935003 / 62500000000) = -Real.log (62500000000 / 128316935003) := by
    rw [show ((128316935003 / 62500000000) : ℝ) = ((62500000000 / 128316935003) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15_neg : (49963691 / 100000000) ≤ -Real.log (125000000000 / 206015343223) ∧
    -Real.log (125000000000 / 206015343223) ≤ (499636911 / 1000000000) := by
  have h := checkLog_sound (w := (81015343223 / 331015343223)) (n := 12)
    (lo := (49963691 / 100000000)) (hi := (499636911 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206015343223 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206015343223 / 125000000000) = 1/(125000000000 / 206015343223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15 : Bounds (49963691 / 100000000) (499636911 / 1000000000) (Real.log (206015343223 / 125000000000)) := by
  have h := reflection_log_15_neg
  have he : Real.log (206015343223 / 125000000000) = -Real.log (125000000000 / 206015343223) := by
    rw [show ((206015343223 / 125000000000) : ℝ) = ((125000000000 / 206015343223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_16_neg : (500534787 / 1000000000) ≤ -Real.log (500000000000 / 824801610959) ∧
    -Real.log (500000000000 / 824801610959) ≤ (125133697 / 250000000) := by
  have h := checkLog_sound (w := (324801610959 / 1324801610959)) (n := 12)
    (lo := (500534787 / 1000000000)) (hi := (125133697 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((824801610959 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(824801610959 / 500000000000) = 1/(500000000000 / 824801610959) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_16 : Bounds (500534787 / 1000000000) (125133697 / 250000000) (Real.log (824801610959 / 500000000000)) := by
  have h := reflection_log_16_neg
  have he : Real.log (824801610959 / 500000000000) = -Real.log (500000000000 / 824801610959) := by
    rw [show ((824801610959 / 500000000000) : ℝ) = ((500000000000 / 824801610959) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_17_neg : (355668511 / 1000000000) ≤ -Real.log (250000000000 / 356783597911) ∧
    -Real.log (250000000000 / 356783597911) ≤ (11114641 / 31250000) := by
  have h := checkLog_sound (w := (106783597911 / 606783597911)) (n := 12)
    (lo := (355668511 / 1000000000)) (hi := (11114641 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356783597911 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356783597911 / 250000000000) = 1/(250000000000 / 356783597911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_17 : Bounds (355668511 / 1000000000) (11114641 / 31250000) (Real.log (356783597911 / 250000000000)) := by
  have h := reflection_log_17_neg
  have he : Real.log (356783597911 / 250000000000) = -Real.log (250000000000 / 356783597911) := by
    rw [show ((356783597911 / 250000000000) : ℝ) = ((250000000000 / 356783597911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_18_neg : (356316619 / 1000000000) ≤ -Real.log (100000000000 / 142805962829) ∧
    -Real.log (100000000000 / 142805962829) ≤ (17815831 / 50000000) := by
  have h := checkLog_sound (w := (42805962829 / 242805962829)) (n := 12)
    (lo := (356316619 / 1000000000)) (hi := (17815831 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142805962829 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142805962829 / 100000000000) = 1/(100000000000 / 142805962829) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_18 : Bounds (356316619 / 1000000000) (17815831 / 50000000) (Real.log (142805962829 / 100000000000)) := by
  have h := reflection_log_18_neg
  have he : Real.log (142805962829 / 100000000000) = -Real.log (100000000000 / 142805962829) := by
    rw [show ((142805962829 / 100000000000) : ℝ) = ((100000000000 / 142805962829) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_19_neg : (15786941 / 500000000) ≤ -Real.log (968919367791 / 1000000000000) ∧
    -Real.log (968919367791 / 1000000000000) ≤ (31573883 / 1000000000) := by
  have h := checkLog_sound (w := (31080632209 / 1968919367791)) (n := 12)
    (lo := (15786941 / 500000000)) (hi := (31573883 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968919367791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968919367791) = 1/(968919367791 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_19 : Bounds (-31573883 / 1000000000) (-15786941 / 500000000) (Real.log (968919367791 / 1000000000000)) := by
  have h := reflection_log_19_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_20_neg : (7864931 / 250000000) ≤ -Real.log (969029983711 / 1000000000000) ∧
    -Real.log (969029983711 / 1000000000000) ≤ (1258389 / 40000000) := by
  have h := checkLog_sound (w := (30970016289 / 1969029983711)) (n := 12)
    (lo := (7864931 / 250000000)) (hi := (1258389 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 969029983711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 969029983711) = 1/(969029983711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_20 : Bounds (-1258389 / 40000000) (-7864931 / 250000000) (Real.log (969029983711 / 1000000000000)) := by
  have h := reflection_log_20_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.DoubleCapHighMiddleDerivative.Cell161

end


