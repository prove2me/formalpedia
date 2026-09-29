-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0025__2
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0025__2
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T21:32:40.878408+00:00
-- url     : https://prove2.me/theorems/f8fba02e-04aa-4b50-9303-222e38cee375
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0025 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0026)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0025 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0026)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0025 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0026)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0025 (+1 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0026) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0025 (+1 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0026).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0025 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1600_neg : (84581241 / 1000000000) ≤ -Real.log (918897 / 1000000) ∧
    -Real.log (918897 / 1000000) ≤ (42290621 / 500000000) := by
  have h := checkLog_sound (w := (81103 / 1918897)) (n := 12)
    (lo := (84581241 / 1000000000)) (hi := (42290621 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918897) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918897) = 1/(918897 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1600 : Bounds (-42290621 / 500000000) (-84581241 / 1000000000) (Real.log (918897 / 1000000)) := by
  have h := reflection_log_1600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1601_neg : (78177893 / 1000000000) ≤ -Real.log (200000 / 216263) ∧
    -Real.log (200000 / 216263) ≤ (39088947 / 500000000) := by
  have h := checkLog_sound (w := (16263 / 416263)) (n := 12)
    (lo := (78177893 / 1000000000)) (hi := (39088947 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216263 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216263 / 200000) = 1/(200000 / 216263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1601 : Bounds (78177893 / 1000000000) (39088947 / 500000000) (Real.log (216263 / 200000)) := by
  have h := reflection_log_1601_neg
  have he : Real.log (216263 / 200000) = -Real.log (200000 / 216263) := by
    rw [show ((216263 / 200000) : ℝ) = ((200000 / 216263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1602_neg : (84811979 / 1000000000) ≤ -Real.log (183737 / 200000) ∧
    -Real.log (183737 / 200000) ≤ (4240599 / 50000000) := by
  have h := checkLog_sound (w := (16263 / 383737)) (n := 12)
    (lo := (84811979 / 1000000000)) (hi := (4240599 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183737) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183737) = 1/(183737 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1602 : Bounds (-4240599 / 50000000) (-84811979 / 1000000000) (Real.log (183737 / 200000)) := by
  have h := reflection_log_1602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1603_neg : (3317043 / 500000000) ≤ -Real.log (39735514831 / 40000000000) ∧
    -Real.log (39735514831 / 40000000000) ≤ (6634087 / 1000000000) := by
  have h := checkLog_sound (w := (264485169 / 79735514831)) (n := 12)
    (lo := (3317043 / 500000000)) (hi := (6634087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735514831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735514831) = 1/(39735514831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1603 : Bounds (-6634087 / 1000000000) (-3317043 / 500000000) (Real.log (39735514831 / 40000000000)) := by
  have h := reflection_log_1603_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1604_neg : (25779 / 3906250) ≤ -Real.log (993422303391 / 1000000000000) ∧
    -Real.log (993422303391 / 1000000000000) ≤ (263977 / 40000000) := by
  have h := checkLog_sound (w := (6577696609 / 1993422303391)) (n := 12)
    (lo := (25779 / 3906250)) (hi := (263977 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993422303391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993422303391) = 1/(993422303391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1604 : Bounds (-263977 / 40000000) (-25779 / 3906250) (Real.log (993422303391 / 1000000000000)) := by
  have h := reflection_log_1604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1605_neg : (162563057 / 1000000000) ≤ -Real.log (500000000000 / 588261252349) ∧
    -Real.log (500000000000 / 588261252349) ≤ (81281529 / 500000000) := by
  have h := checkLog_sound (w := (88261252349 / 1088261252349)) (n := 12)
    (lo := (162563057 / 1000000000)) (hi := (81281529 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588261252349 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588261252349 / 500000000000) = 1/(500000000000 / 588261252349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1605 : Bounds (162563057 / 1000000000) (81281529 / 500000000) (Real.log (588261252349 / 500000000000)) := by
  have h := reflection_log_1605_neg
  have he : Real.log (588261252349 / 500000000000) = -Real.log (500000000000 / 588261252349) := by
    rw [show ((588261252349 / 500000000000) : ℝ) = ((500000000000 / 588261252349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1606_neg : (10186867 / 62500000) ≤ -Real.log (10000000000 / 11770247691) ∧
    -Real.log (10000000000 / 11770247691) ≤ (162989873 / 1000000000) := by
  have h := checkLog_sound (w := (1770247691 / 21770247691)) (n := 12)
    (lo := (10186867 / 62500000)) (hi := (162989873 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11770247691 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11770247691 / 10000000000) = 1/(10000000000 / 11770247691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1606 : Bounds (10186867 / 62500000) (162989873 / 1000000000) (Real.log (11770247691 / 10000000000)) := by
  have h := reflection_log_1606_neg
  have he : Real.log (11770247691 / 10000000000) = -Real.log (10000000000 / 11770247691) := by
    rw [show ((11770247691 / 10000000000) : ℝ) = ((10000000000 / 11770247691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1607_neg : (32605833 / 100000000) ≤ -Real.log (500000000000 / 692748091603) ∧
    -Real.log (500000000000 / 692748091603) ≤ (326058331 / 1000000000) := by
  have h := checkLog_sound (w := (192748091603 / 1192748091603)) (n := 12)
    (lo := (32605833 / 100000000)) (hi := (326058331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((692748091603 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(692748091603 / 500000000000) = 1/(500000000000 / 692748091603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1607 : Bounds (32605833 / 100000000) (326058331 / 1000000000) (Real.log (692748091603 / 500000000000)) := by
  have h := reflection_log_1607_neg
  have he : Real.log (692748091603 / 500000000000) = -Real.log (500000000000 / 692748091603) := by
    rw [show ((692748091603 / 500000000000) : ℝ) = ((500000000000 / 692748091603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1608_neg : (20391481 / 62500000) ≤ -Real.log (4000000000 / 5543122987) ∧
    -Real.log (4000000000 / 5543122987) ≤ (326263697 / 1000000000) := by
  have h := checkLog_sound (w := (1543122987 / 9543122987)) (n := 12)
    (lo := (20391481 / 62500000)) (hi := (326263697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5543122987 / 4000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5543122987 / 4000000000) = 1/(4000000000 / 5543122987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1608 : Bounds (20391481 / 62500000) (326263697 / 1000000000) (Real.log (5543122987 / 4000000000)) := by
  have h := reflection_log_1608_neg
  have he : Real.log (5543122987 / 4000000000) = -Real.log (4000000000 / 5543122987) := by
    rw [show ((5543122987 / 4000000000) : ℝ) = ((4000000000 / 5543122987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1609_neg : (74985263 / 500000000) ≤ -Real.log (5000 / 5809) ∧
    -Real.log (5000 / 5809) ≤ (149970527 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 10809)) (n := 12)
    (lo := (74985263 / 500000000)) (hi := (149970527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5809 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5809 / 5000) = 1/(5000 / 5809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1609 : Bounds (74985263 / 500000000) (149970527 / 1000000000) (Real.log (5809 / 5000)) := by
  have h := reflection_log_1609_neg
  have he : Real.log (5809 / 5000) = -Real.log (5000 / 5809) := by
    rw [show ((5809 / 5000) : ℝ) = ((5000 / 5809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1610_neg : (176498543 / 1000000000) ≤ -Real.log (4191 / 5000) ∧
    -Real.log (4191 / 5000) ≤ (11031159 / 62500000) := by
  have h := checkLog_sound (w := (809 / 9191)) (n := 12)
    (lo := (176498543 / 1000000000)) (hi := (11031159 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4191) = 1/(4191 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1610 : Bounds (-11031159 / 62500000) (-176498543 / 1000000000) (Real.log (4191 / 5000)) := by
  have h := reflection_log_1610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1611_neg : (80893 / 500000000) ≤ -Real.log (5000000 / 5000809) ∧
    -Real.log (5000000 / 5000809) ≤ (161787 / 1000000000) := by
  have h := checkLog_sound (w := (809 / 10000809)) (n := 12)
    (lo := (80893 / 500000000)) (hi := (161787 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000809 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000809 / 5000000) = 1/(5000000 / 5000809) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1611 : Bounds (80893 / 500000000) (161787 / 1000000000) (Real.log (5000809 / 5000000)) := by
  have h := reflection_log_1611_neg
  have he : Real.log (5000809 / 5000000) = -Real.log (5000000 / 5000809) := by
    rw [show ((5000809 / 5000000) : ℝ) = ((5000000 / 5000809) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1612_neg : (161813 / 1000000000) ≤ -Real.log (4999191 / 5000000) ∧
    -Real.log (4999191 / 5000000) ≤ (80907 / 500000000) := by
  have h := checkLog_sound (w := (809 / 9999191)) (n := 12)
    (lo := (161813 / 1000000000)) (hi := (80907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999191) = 1/(4999191 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1612 : Bounds (-80907 / 500000000) (-161813 / 1000000000) (Real.log (4999191 / 5000000)) := by
  have h := reflection_log_1612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1613_neg : (2438377 / 31250000) ≤ -Real.log (1000000 / 1081153) ∧
    -Real.log (1000000 / 1081153) ≤ (15605613 / 200000000) := by
  have h := checkLog_sound (w := (81153 / 2081153)) (n := 12)
    (lo := (2438377 / 31250000)) (hi := (15605613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081153 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081153 / 1000000) = 1/(1000000 / 1081153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1613 : Bounds (2438377 / 31250000) (15605613 / 200000000) (Real.log (1081153 / 1000000)) := by
  have h := reflection_log_1613_neg
  have he : Real.log (1081153 / 1000000) = -Real.log (1000000 / 1081153) := by
    rw [show ((1081153 / 1000000) : ℝ) = ((1000000 / 1081153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1614_neg : (16927131 / 200000000) ≤ -Real.log (918847 / 1000000) ∧
    -Real.log (918847 / 1000000) ≤ (10579457 / 125000000) := by
  have h := checkLog_sound (w := (81153 / 1918847)) (n := 12)
    (lo := (16927131 / 200000000)) (hi := (10579457 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918847) = 1/(918847 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1614 : Bounds (-10579457 / 125000000) (-16927131 / 200000000) (Real.log (918847 / 1000000)) := by
  have h := reflection_log_1614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1615_neg : (2444533 / 31250000) ≤ -Real.log (500000 / 540683) ∧
    -Real.log (500000 / 540683) ≤ (78225057 / 1000000000) := by
  have h := checkLog_sound (w := (40683 / 1040683)) (n := 12)
    (lo := (2444533 / 31250000)) (hi := (78225057 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540683 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540683 / 500000) = 1/(500000 / 540683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1615 : Bounds (2444533 / 31250000) (78225057 / 1000000000) (Real.log (540683 / 500000)) := by
  have h := reflection_log_1615_neg
  have he : Real.log (540683 / 500000) = -Real.log (500000 / 540683) := by
    rw [show ((540683 / 500000) : ℝ) = ((500000 / 540683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1616_neg : (42433747 / 500000000) ≤ -Real.log (459317 / 500000) ∧
    -Real.log (459317 / 500000) ≤ (16973499 / 200000000) := by
  have h := checkLog_sound (w := (40683 / 959317)) (n := 12)
    (lo := (42433747 / 500000000)) (hi := (16973499 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459317) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459317) = 1/(459317 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1616 : Bounds (-16973499 / 200000000) (-42433747 / 500000000) (Real.log (459317 / 500000)) := by
  have h := reflection_log_1616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1617_neg : (3321219 / 500000000) ≤ -Real.log (248344893511 / 250000000000) ∧
    -Real.log (248344893511 / 250000000000) ≤ (6642439 / 1000000000) := by
  have h := checkLog_sound (w := (1655106489 / 498344893511)) (n := 12)
    (lo := (3321219 / 500000000)) (hi := (6642439 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248344893511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248344893511) = 1/(248344893511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1617 : Bounds (-6642439 / 1000000000) (-3321219 / 500000000) (Real.log (248344893511 / 250000000000)) := by
  have h := reflection_log_1617_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1618_neg : (6607591 / 1000000000) ≤ -Real.log (993414190591 / 1000000000000) ∧
    -Real.log (993414190591 / 1000000000000) ≤ (825949 / 125000000) := by
  have h := checkLog_sound (w := (6585809409 / 1993414190591)) (n := 12)
    (lo := (6607591 / 1000000000)) (hi := (825949 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993414190591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993414190591) = 1/(993414190591 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1618 : Bounds (-825949 / 125000000) (-6607591 / 1000000000) (Real.log (993414190591 / 1000000000000)) := by
  have h := reflection_log_1618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1619_neg : (4066593 / 25000000) ≤ -Real.log (500000000000 / 588320471199) ∧
    -Real.log (500000000000 / 588320471199) ≤ (162663721 / 1000000000) := by
  have h := checkLog_sound (w := (88320471199 / 1088320471199)) (n := 12)
    (lo := (4066593 / 25000000)) (hi := (162663721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588320471199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588320471199 / 500000000000) = 1/(500000000000 / 588320471199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1619 : Bounds (4066593 / 25000000) (162663721 / 1000000000) (Real.log (588320471199 / 500000000000)) := by
  have h := reflection_log_1619_neg
  have he : Real.log (588320471199 / 500000000000) = -Real.log (500000000000 / 588320471199) := by
    rw [show ((588320471199 / 500000000000) : ℝ) = ((500000000000 / 588320471199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1620_neg : (163092551 / 1000000000) ≤ -Real.log (20000000000 / 23542912629) ∧
    -Real.log (20000000000 / 23542912629) ≤ (20386569 / 125000000) := by
  have h := checkLog_sound (w := (3542912629 / 43542912629)) (n := 12)
    (lo := (163092551 / 1000000000)) (hi := (20386569 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((23542912629 / 20000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(23542912629 / 20000000000) = 1/(20000000000 / 23542912629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1620 : Bounds (163092551 / 1000000000) (20386569 / 125000000) (Real.log (23542912629 / 20000000000)) := by
  have h := reflection_log_1620_neg
  have he : Real.log (23542912629 / 20000000000) = -Real.log (20000000000 / 23542912629) := by
    rw [show ((23542912629 / 20000000000) : ℝ) = ((20000000000 / 23542912629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1621_neg : (20391481 / 62500000) ≤ -Real.log (250000000000 / 346445186687) ∧
    -Real.log (250000000000 / 346445186687) ≤ (326263697 / 1000000000) := by
  have h := checkLog_sound (w := (96445186687 / 596445186687)) (n := 12)
    (lo := (20391481 / 62500000)) (hi := (326263697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346445186687 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346445186687 / 250000000000) = 1/(250000000000 / 346445186687) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1621 : Bounds (20391481 / 62500000) (326263697 / 1000000000) (Real.log (346445186687 / 250000000000)) := by
  have h := reflection_log_1621_neg
  have he : Real.log (346445186687 / 250000000000) = -Real.log (250000000000 / 346445186687) := by
    rw [show ((346445186687 / 250000000000) : ℝ) = ((250000000000 / 346445186687) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1622_neg : (32646907 / 100000000) ≤ -Real.log (62500000000 / 86629086137) ∧
    -Real.log (62500000000 / 86629086137) ≤ (326469071 / 1000000000) := by
  have h := checkLog_sound (w := (24129086137 / 149129086137)) (n := 12)
    (lo := (32646907 / 100000000)) (hi := (326469071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((86629086137 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(86629086137 / 62500000000) = 1/(62500000000 / 86629086137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1622 : Bounds (32646907 / 100000000) (326469071 / 1000000000) (Real.log (86629086137 / 62500000000)) := by
  have h := reflection_log_1622_neg
  have he : Real.log (86629086137 / 62500000000) = -Real.log (62500000000 / 86629086137) := by
    rw [show ((86629086137 / 62500000000) : ℝ) = ((62500000000 / 86629086137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1623_neg : (37514149 / 250000000) ≤ -Real.log (10000 / 11619) ∧
    -Real.log (10000 / 11619) ≤ (150056597 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 21619)) (n := 12)
    (lo := (37514149 / 250000000)) (hi := (150056597 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11619 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11619 / 10000) = 1/(10000 / 11619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1623 : Bounds (37514149 / 250000000) (150056597 / 1000000000) (Real.log (11619 / 10000)) := by
  have h := reflection_log_1623_neg
  have he : Real.log (11619 / 10000) = -Real.log (10000 / 11619) := by
    rw [show ((11619 / 10000) : ℝ) = ((10000 / 11619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1624_neg : (176617853 / 1000000000) ≤ -Real.log (8381 / 10000) ∧
    -Real.log (8381 / 10000) ≤ (88308927 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 18381)) (n := 12)
    (lo := (176617853 / 1000000000)) (hi := (88308927 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8381) = 1/(8381 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1624 : Bounds (-88308927 / 500000000) (-176617853 / 1000000000) (Real.log (8381 / 10000)) := by
  have h := reflection_log_1624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1625_neg : (80943 / 500000000) ≤ -Real.log (10000000 / 10001619) ∧
    -Real.log (10000000 / 10001619) ≤ (161887 / 1000000000) := by
  have h := checkLog_sound (w := (1619 / 20001619)) (n := 12)
    (lo := (80943 / 500000000)) (hi := (161887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001619 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001619 / 10000000) = 1/(10000000 / 10001619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1625 : Bounds (80943 / 500000000) (161887 / 1000000000) (Real.log (10001619 / 10000000)) := by
  have h := reflection_log_1625_neg
  have he : Real.log (10001619 / 10000000) = -Real.log (10000000 / 10001619) := by
    rw [show ((10001619 / 10000000) : ℝ) = ((10000000 / 10001619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1626_neg : (161913 / 1000000000) ≤ -Real.log (9998381 / 10000000) ∧
    -Real.log (9998381 / 10000000) ≤ (80957 / 500000000) := by
  have h := checkLog_sound (w := (1619 / 19998381)) (n := 12)
    (lo := (161913 / 1000000000)) (hi := (80957 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998381) = 1/(9998381 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1626 : Bounds (-80957 / 500000000) (-161913 / 1000000000) (Real.log (9998381 / 10000000)) := by
  have h := reflection_log_1626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1627_neg : (15615047 / 200000000) ≤ -Real.log (250000 / 270301) ∧
    -Real.log (250000 / 270301) ≤ (19518809 / 250000000) := by
  have h := checkLog_sound (w := (20301 / 520301)) (n := 12)
    (lo := (15615047 / 200000000)) (hi := (19518809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270301 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270301 / 250000) = 1/(250000 / 270301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1627 : Bounds (15615047 / 200000000) (19518809 / 250000000) (Real.log (270301 / 250000)) := by
  have h := reflection_log_1627_neg
  have he : Real.log (270301 / 250000) = -Real.log (250000 / 270301) := by
    rw [show ((270301 / 250000) : ℝ) = ((250000 / 270301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1628_neg : (84691161 / 1000000000) ≤ -Real.log (229699 / 250000) ∧
    -Real.log (229699 / 250000) ≤ (42345581 / 500000000) := by
  have h := checkLog_sound (w := (20301 / 479699)) (n := 12)
    (lo := (84691161 / 1000000000)) (hi := (42345581 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229699) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229699) = 1/(229699 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1628 : Bounds (-42345581 / 500000000) (-84691161 / 1000000000) (Real.log (229699 / 250000)) := by
  have h := reflection_log_1628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1629_neg : (39136109 / 500000000) ≤ -Real.log (1000000 / 1081417) ∧
    -Real.log (1000000 / 1081417) ≤ (78272219 / 1000000000) := by
  have h := checkLog_sound (w := (81417 / 2081417)) (n := 12)
    (lo := (39136109 / 500000000)) (hi := (78272219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081417 / 1000000) = 1/(1000000 / 1081417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1629 : Bounds (39136109 / 500000000) (78272219 / 1000000000) (Real.log (1081417 / 1000000)) := by
  have h := reflection_log_1629_neg
  have he : Real.log (1081417 / 1000000) = -Real.log (1000000 / 1081417) := by
    rw [show ((1081417 / 1000000) : ℝ) = ((1000000 / 1081417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1630_neg : (84923013 / 1000000000) ≤ -Real.log (918583 / 1000000) ∧
    -Real.log (918583 / 1000000) ≤ (42461507 / 500000000) := by
  have h := checkLog_sound (w := (81417 / 1918583)) (n := 12)
    (lo := (84923013 / 1000000000)) (hi := (42461507 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918583) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918583) = 1/(918583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1630 : Bounds (-42461507 / 500000000) (-84923013 / 1000000000) (Real.log (918583 / 1000000)) := by
  have h := reflection_log_1630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1631_neg : (1330159 / 200000000) ≤ -Real.log (993371272111 / 1000000000000) ∧
    -Real.log (993371272111 / 1000000000000) ≤ (1662699 / 250000000) := by
  have h := checkLog_sound (w := (6628727889 / 1993371272111)) (n := 12)
    (lo := (1330159 / 200000000)) (hi := (1662699 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993371272111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993371272111) = 1/(993371272111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1631 : Bounds (-1662699 / 250000000) (-1330159 / 200000000) (Real.log (993371272111 / 1000000000000)) := by
  have h := reflection_log_1631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1632_neg : (3307963 / 500000000) ≤ -Real.log (62087869399 / 62500000000) ∧
    -Real.log (62087869399 / 62500000000) ≤ (6615927 / 1000000000) := by
  have h := checkLog_sound (w := (412130601 / 124587869399)) (n := 12)
    (lo := (3307963 / 500000000)) (hi := (6615927 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62087869399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62087869399) = 1/(62087869399 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1632 : Bounds (-6615927 / 1000000000) (-3307963 / 500000000) (Real.log (62087869399 / 62500000000)) := by
  have h := reflection_log_1632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1633_neg : (40691599 / 250000000) ≤ -Real.log (250000000000 / 294190440533) ∧
    -Real.log (250000000000 / 294190440533) ≤ (162766397 / 1000000000) := by
  have h := checkLog_sound (w := (44190440533 / 544190440533)) (n := 12)
    (lo := (40691599 / 250000000)) (hi := (162766397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294190440533 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294190440533 / 250000000000) = 1/(250000000000 / 294190440533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1633 : Bounds (40691599 / 250000000) (162766397 / 1000000000) (Real.log (294190440533 / 250000000000)) := by
  have h := reflection_log_1633_neg
  have he : Real.log (294190440533 / 250000000000) = -Real.log (250000000000 / 294190440533) := by
    rw [show ((294190440533 / 250000000000) : ℝ) = ((250000000000 / 294190440533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1634_neg : (163195231 / 1000000000) ≤ -Real.log (50000000000 / 58863325361) ∧
    -Real.log (50000000000 / 58863325361) ≤ (5099851 / 31250000) := by
  have h := checkLog_sound (w := (8863325361 / 108863325361)) (n := 12)
    (lo := (163195231 / 1000000000)) (hi := (5099851 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58863325361 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58863325361 / 50000000000) = 1/(50000000000 / 58863325361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1634 : Bounds (163195231 / 1000000000) (5099851 / 31250000) (Real.log (58863325361 / 50000000000)) := by
  have h := reflection_log_1634_neg
  have he : Real.log (58863325361 / 50000000000) = -Real.log (50000000000 / 58863325361) := by
    rw [show ((58863325361 / 50000000000) : ℝ) = ((50000000000 / 58863325361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1635_neg : (32646907 / 100000000) ≤ -Real.log (100000000000 / 138606537819) ∧
    -Real.log (100000000000 / 138606537819) ≤ (326469071 / 1000000000) := by
  have h := checkLog_sound (w := (38606537819 / 238606537819)) (n := 12)
    (lo := (32646907 / 100000000)) (hi := (326469071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138606537819 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138606537819 / 100000000000) = 1/(100000000000 / 138606537819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1635 : Bounds (32646907 / 100000000) (326469071 / 1000000000) (Real.log (138606537819 / 100000000000)) := by
  have h := reflection_log_1635_neg
  have he : Real.log (138606537819 / 100000000000) = -Real.log (100000000000 / 138606537819) := by
    rw [show ((138606537819 / 100000000000) : ℝ) = ((100000000000 / 138606537819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1636_neg : (6533489 / 20000000) ≤ -Real.log (500000000000 / 693175038779) ∧
    -Real.log (500000000000 / 693175038779) ≤ (326674451 / 1000000000) := by
  have h := checkLog_sound (w := (193175038779 / 1193175038779)) (n := 12)
    (lo := (6533489 / 20000000)) (hi := (326674451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693175038779 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693175038779 / 500000000000) = 1/(500000000000 / 693175038779) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1636 : Bounds (6533489 / 20000000) (326674451 / 1000000000) (Real.log (693175038779 / 500000000000)) := by
  have h := reflection_log_1636_neg
  have he : Real.log (693175038779 / 500000000000) = -Real.log (500000000000 / 693175038779) := by
    rw [show ((693175038779 / 500000000000) : ℝ) = ((500000000000 / 693175038779) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1637_neg : (75071329 / 500000000) ≤ -Real.log (500 / 581) ∧
    -Real.log (500 / 581) ≤ (150142659 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1081)) (n := 12)
    (lo := (75071329 / 500000000)) (hi := (150142659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((581 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(581 / 500) = 1/(500 / 581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1637 : Bounds (75071329 / 500000000) (150142659 / 1000000000) (Real.log (581 / 500)) := by
  have h := reflection_log_1637_neg
  have he : Real.log (581 / 500) = -Real.log (500 / 581) := by
    rw [show ((581 / 500) : ℝ) = ((500 / 581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1638_neg : (88368589 / 500000000) ≤ -Real.log (419 / 500) ∧
    -Real.log (419 / 500) ≤ (176737179 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 919)) (n := 12)
    (lo := (88368589 / 500000000)) (hi := (176737179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 419) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 419) = 1/(419 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1638 : Bounds (-176737179 / 1000000000) (-88368589 / 500000000) (Real.log (419 / 500)) := by
  have h := reflection_log_1638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1639_neg : (80993 / 500000000) ≤ -Real.log (500000 / 500081) ∧
    -Real.log (500000 / 500081) ≤ (161987 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1000081)) (n := 12)
    (lo := (80993 / 500000000)) (hi := (161987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500081 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500081 / 500000) = 1/(500000 / 500081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1639 : Bounds (80993 / 500000000) (161987 / 1000000000) (Real.log (500081 / 500000)) := by
  have h := reflection_log_1639_neg
  have he : Real.log (500081 / 500000) = -Real.log (500000 / 500081) := by
    rw [show ((500081 / 500000) : ℝ) = ((500000 / 500081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1640_neg : (162013 / 1000000000) ≤ -Real.log (499919 / 500000) ∧
    -Real.log (499919 / 500000) ≤ (81007 / 500000000) := by
  have h := checkLog_sound (w := (81 / 999919)) (n := 12)
    (lo := (162013 / 1000000000)) (hi := (81007 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499919) = 1/(499919 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1640 : Bounds (-81007 / 500000000) (-162013 / 1000000000) (Real.log (499919 / 500000)) := by
  have h := reflection_log_1640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1641_neg : (78122403 / 1000000000) ≤ -Real.log (200000 / 216251) ∧
    -Real.log (200000 / 216251) ≤ (19530601 / 250000000) := by
  have h := checkLog_sound (w := (16251 / 416251)) (n := 12)
    (lo := (78122403 / 1000000000)) (hi := (19530601 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216251 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216251 / 200000) = 1/(200000 / 216251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1641 : Bounds (78122403 / 1000000000) (19530601 / 250000000) (Real.log (216251 / 200000)) := by
  have h := reflection_log_1641_neg
  have he : Real.log (216251 / 200000) = -Real.log (200000 / 216251) := by
    rw [show ((216251 / 200000) : ℝ) = ((200000 / 216251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1642_neg : (8474667 / 100000000) ≤ -Real.log (183749 / 200000) ∧
    -Real.log (183749 / 200000) ≤ (84746671 / 1000000000) := by
  have h := checkLog_sound (w := (16251 / 383749)) (n := 12)
    (lo := (8474667 / 100000000)) (hi := (84746671 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183749) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183749) = 1/(183749 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1642 : Bounds (-84746671 / 1000000000) (-8474667 / 100000000) (Real.log (183749 / 200000)) := by
  have h := reflection_log_1642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1643_neg : (19579613 / 250000000) ≤ -Real.log (1000000 / 1081467) ∧
    -Real.log (1000000 / 1081467) ≤ (78318453 / 1000000000) := by
  have h := checkLog_sound (w := (81467 / 2081467)) (n := 12)
    (lo := (19579613 / 250000000)) (hi := (78318453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081467 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081467 / 1000000) = 1/(1000000 / 1081467) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1643 : Bounds (19579613 / 250000000) (78318453 / 1000000000) (Real.log (1081467 / 1000000)) := by
  have h := reflection_log_1643_neg
  have he : Real.log (1081467 / 1000000) = -Real.log (1000000 / 1081467) := by
    rw [show ((1081467 / 1000000) : ℝ) = ((1000000 / 1081467) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1644_neg : (42488723 / 500000000) ≤ -Real.log (918533 / 1000000) ∧
    -Real.log (918533 / 1000000) ≤ (84977447 / 1000000000) := by
  have h := checkLog_sound (w := (81467 / 1918533)) (n := 12)
    (lo := (42488723 / 500000000)) (hi := (84977447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918533) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918533) = 1/(918533 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1644 : Bounds (-84977447 / 1000000000) (-42488723 / 500000000) (Real.log (918533 / 1000000)) := by
  have h := reflection_log_1644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1645_neg : (3329497 / 500000000) ≤ -Real.log (993363127911 / 1000000000000) ∧
    -Real.log (993363127911 / 1000000000000) ≤ (1331799 / 200000000) := by
  have h := checkLog_sound (w := (6636872089 / 1993363127911)) (n := 12)
    (lo := (3329497 / 500000000)) (hi := (1331799 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993363127911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993363127911) = 1/(993363127911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1645 : Bounds (-1331799 / 200000000) (-3329497 / 500000000) (Real.log (993363127911 / 1000000000000)) := by
  have h := reflection_log_1645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1646_neg : (6624267 / 1000000000) ≤ -Real.log (39735904999 / 40000000000) ∧
    -Real.log (39735904999 / 40000000000) ≤ (1656067 / 250000000) := by
  have h := checkLog_sound (w := (264095001 / 79735904999)) (n := 12)
    (lo := (6624267 / 1000000000)) (hi := (1656067 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735904999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735904999) = 1/(39735904999 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1646 : Bounds (-1656067 / 250000000) (-6624267 / 1000000000) (Real.log (39735904999 / 40000000000)) := by
  have h := reflection_log_1646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1647_neg : (81434537 / 500000000) ≤ -Real.log (500000000000 / 588441297639) ∧
    -Real.log (500000000000 / 588441297639) ≤ (6514763 / 40000000) := by
  have h := checkLog_sound (w := (88441297639 / 1088441297639)) (n := 12)
    (lo := (81434537 / 500000000)) (hi := (6514763 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588441297639 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588441297639 / 500000000000) = 1/(500000000000 / 588441297639) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1647 : Bounds (81434537 / 500000000) (6514763 / 40000000) (Real.log (588441297639 / 500000000000)) := by
  have h := reflection_log_1647_neg
  have he : Real.log (588441297639 / 500000000000) = -Real.log (500000000000 / 588441297639) := by
    rw [show ((588441297639 / 500000000000) : ℝ) = ((500000000000 / 588441297639) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1648_neg : (163295899 / 1000000000) ≤ -Real.log (500000000000 / 588692512953) ∧
    -Real.log (500000000000 / 588692512953) ≤ (1632959 / 10000000) := by
  have h := checkLog_sound (w := (88692512953 / 1088692512953)) (n := 12)
    (lo := (163295899 / 1000000000)) (hi := (1632959 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588692512953 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588692512953 / 500000000000) = 1/(500000000000 / 588692512953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1648 : Bounds (163295899 / 1000000000) (1632959 / 10000000) (Real.log (588692512953 / 500000000000)) := by
  have h := reflection_log_1648_neg
  have he : Real.log (588692512953 / 500000000000) = -Real.log (500000000000 / 588692512953) := by
    rw [show ((588692512953 / 500000000000) : ℝ) = ((500000000000 / 588692512953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1649_neg : (6533489 / 20000000) ≤ -Real.log (250000000000 / 346587519389) ∧
    -Real.log (250000000000 / 346587519389) ≤ (326674451 / 1000000000) := by
  have h := checkLog_sound (w := (96587519389 / 596587519389)) (n := 12)
    (lo := (6533489 / 20000000)) (hi := (326674451 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346587519389 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346587519389 / 250000000000) = 1/(250000000000 / 346587519389) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1649 : Bounds (6533489 / 20000000) (326674451 / 1000000000) (Real.log (346587519389 / 250000000000)) := by
  have h := reflection_log_1649_neg
  have he : Real.log (346587519389 / 250000000000) = -Real.log (250000000000 / 346587519389) := by
    rw [show ((346587519389 / 250000000000) : ℝ) = ((250000000000 / 346587519389) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1650_neg : (81719959 / 250000000) ≤ -Real.log (100000000000 / 138663484487) ∧
    -Real.log (100000000000 / 138663484487) ≤ (326879837 / 1000000000) := by
  have h := checkLog_sound (w := (38663484487 / 238663484487)) (n := 12)
    (lo := (81719959 / 250000000)) (hi := (326879837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138663484487 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(138663484487 / 100000000000) = 1/(100000000000 / 138663484487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1650 : Bounds (81719959 / 250000000) (326879837 / 1000000000) (Real.log (138663484487 / 100000000000)) := by
  have h := reflection_log_1650_neg
  have he : Real.log (138663484487 / 100000000000) = -Real.log (100000000000 / 138663484487) := by
    rw [show ((138663484487 / 100000000000) : ℝ) = ((100000000000 / 138663484487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1651_neg : (150228713 / 1000000000) ≤ -Real.log (10000 / 11621) ∧
    -Real.log (10000 / 11621) ≤ (75114357 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 21621)) (n := 12)
    (lo := (150228713 / 1000000000)) (hi := (75114357 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11621 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11621 / 10000) = 1/(10000 / 11621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1651 : Bounds (150228713 / 1000000000) (75114357 / 500000000) (Real.log (11621 / 10000)) := by
  have h := reflection_log_1651_neg
  have he : Real.log (11621 / 10000) = -Real.log (10000 / 11621) := by
    rw [show ((11621 / 10000) : ℝ) = ((10000 / 11621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1652_neg : (176856517 / 1000000000) ≤ -Real.log (8379 / 10000) ∧
    -Real.log (8379 / 10000) ≤ (88428259 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 18379)) (n := 12)
    (lo := (176856517 / 1000000000)) (hi := (88428259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8379) = 1/(8379 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1652 : Bounds (-88428259 / 500000000) (-176856517 / 1000000000) (Real.log (8379 / 10000)) := by
  have h := reflection_log_1652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1653_neg : (81043 / 500000000) ≤ -Real.log (10000000 / 10001621) ∧
    -Real.log (10000000 / 10001621) ≤ (162087 / 1000000000) := by
  have h := checkLog_sound (w := (1621 / 20001621)) (n := 12)
    (lo := (81043 / 500000000)) (hi := (162087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001621 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001621 / 10000000) = 1/(10000000 / 10001621) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1653 : Bounds (81043 / 500000000) (162087 / 1000000000) (Real.log (10001621 / 10000000)) := by
  have h := reflection_log_1653_neg
  have he : Real.log (10001621 / 10000000) = -Real.log (10000000 / 10001621) := by
    rw [show ((10001621 / 10000000) : ℝ) = ((10000000 / 10001621) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1654_neg : (162113 / 1000000000) ≤ -Real.log (9998379 / 10000000) ∧
    -Real.log (9998379 / 10000000) ≤ (81057 / 500000000) := by
  have h := checkLog_sound (w := (1621 / 19998379)) (n := 12)
    (lo := (162113 / 1000000000)) (hi := (81057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998379) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998379) = 1/(9998379 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1654 : Bounds (-81057 / 500000000) (-162113 / 1000000000) (Real.log (9998379 / 10000000)) := by
  have h := reflection_log_1654_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1655_neg : (15633729 / 200000000) ≤ -Real.log (200000 / 216261) ∧
    -Real.log (200000 / 216261) ≤ (39084323 / 500000000) := by
  have h := checkLog_sound (w := (16261 / 416261)) (n := 12)
    (lo := (15633729 / 200000000)) (hi := (39084323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((216261 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(216261 / 200000) = 1/(200000 / 216261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1655 : Bounds (15633729 / 200000000) (39084323 / 500000000) (Real.log (216261 / 200000)) := by
  have h := reflection_log_1655_neg
  have he : Real.log (216261 / 200000) = -Real.log (200000 / 216261) := by
    rw [show ((216261 / 200000) : ℝ) = ((200000 / 216261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1656_neg : (42400547 / 500000000) ≤ -Real.log (183739 / 200000) ∧
    -Real.log (183739 / 200000) ≤ (16960219 / 200000000) := by
  have h := checkLog_sound (w := (16261 / 383739)) (n := 12)
    (lo := (42400547 / 500000000)) (hi := (16960219 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 183739) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 183739) = 1/(183739 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1656 : Bounds (-16960219 / 200000000) (-42400547 / 500000000) (Real.log (183739 / 200000)) := by
  have h := reflection_log_1656_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1657_neg : (78365609 / 1000000000) ≤ -Real.log (500000 / 540759) ∧
    -Real.log (500000 / 540759) ≤ (7836561 / 100000000) := by
  have h := checkLog_sound (w := (40759 / 1040759)) (n := 12)
    (lo := (78365609 / 1000000000)) (hi := (7836561 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((540759 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(540759 / 500000) = 1/(500000 / 540759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1657 : Bounds (78365609 / 1000000000) (7836561 / 100000000) (Real.log (540759 / 500000)) := by
  have h := reflection_log_1657_neg
  have he : Real.log (540759 / 500000) = -Real.log (500000 / 540759) := by
    rw [show ((540759 / 500000) : ℝ) = ((500000 / 540759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1658_neg : (85032971 / 1000000000) ≤ -Real.log (459241 / 500000) ∧
    -Real.log (459241 / 500000) ≤ (21258243 / 250000000) := by
  have h := checkLog_sound (w := (40759 / 959241)) (n := 12)
    (lo := (85032971 / 1000000000)) (hi := (21258243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 459241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 459241) = 1/(459241 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1658 : Bounds (-21258243 / 250000000) (-85032971 / 1000000000) (Real.log (459241 / 500000)) := by
  have h := reflection_log_1658_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1659_neg : (6667361 / 1000000000) ≤ -Real.log (248338703919 / 250000000000) ∧
    -Real.log (248338703919 / 250000000000) ≤ (3333681 / 500000000) := by
  have h := checkLog_sound (w := (1661296081 / 498338703919)) (n := 12)
    (lo := (6667361 / 1000000000)) (hi := (3333681 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248338703919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248338703919) = 1/(248338703919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1659 : Bounds (-3333681 / 500000000) (-6667361 / 1000000000) (Real.log (248338703919 / 250000000000)) := by
  have h := reflection_log_1659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1660_neg : (6632449 / 1000000000) ≤ -Real.log (39735579879 / 40000000000) ∧
    -Real.log (39735579879 / 40000000000) ≤ (132649 / 20000000) := by
  have h := checkLog_sound (w := (264420121 / 79735579879)) (n := 12)
    (lo := (6632449 / 1000000000)) (hi := (132649 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39735579879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39735579879) = 1/(39735579879 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1660 : Bounds (-132649 / 20000000) (-6632449 / 1000000000) (Real.log (39735579879 / 40000000000)) := by
  have h := reflection_log_1660_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1661_neg : (162969739 / 1000000000) ≤ -Real.log (250000000000 / 294250268043) ∧
    -Real.log (250000000000 / 294250268043) ≤ (8148487 / 50000000) := by
  have h := checkLog_sound (w := (44250268043 / 544250268043)) (n := 12)
    (lo := (162969739 / 1000000000)) (hi := (8148487 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294250268043 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294250268043 / 250000000000) = 1/(250000000000 / 294250268043) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1661 : Bounds (162969739 / 1000000000) (8148487 / 50000000) (Real.log (294250268043 / 250000000000)) := by
  have h := reflection_log_1661_neg
  have he : Real.log (294250268043 / 250000000000) = -Real.log (250000000000 / 294250268043) := by
    rw [show ((294250268043 / 250000000000) : ℝ) = ((250000000000 / 294250268043) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1662_neg : (163398581 / 1000000000) ≤ -Real.log (50000000000 / 58875296413) ∧
    -Real.log (50000000000 / 58875296413) ≤ (81699291 / 500000000) := by
  have h := checkLog_sound (w := (8875296413 / 108875296413)) (n := 12)
    (lo := (163398581 / 1000000000)) (hi := (81699291 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((58875296413 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(58875296413 / 50000000000) = 1/(50000000000 / 58875296413) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1662 : Bounds (163398581 / 1000000000) (81699291 / 500000000) (Real.log (58875296413 / 50000000000)) := by
  have h := reflection_log_1662_neg
  have he : Real.log (58875296413 / 50000000000) = -Real.log (50000000000 / 58875296413) := by
    rw [show ((58875296413 / 50000000000) : ℝ) = ((50000000000 / 58875296413) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1663_neg : (81719959 / 250000000) ≤ -Real.log (250000000000 / 346658711217) ∧
    -Real.log (250000000000 / 346658711217) ≤ (326879837 / 1000000000) := by
  have h := checkLog_sound (w := (96658711217 / 596658711217)) (n := 12)
    (lo := (81719959 / 250000000)) (hi := (326879837 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346658711217 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346658711217 / 250000000000) = 1/(250000000000 / 346658711217) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1663 : Bounds (81719959 / 250000000) (326879837 / 1000000000) (Real.log (346658711217 / 250000000000)) := by
  have h := reflection_log_1663_neg
  have he : Real.log (346658711217 / 250000000000) = -Real.log (250000000000 / 346658711217) := by
    rw [show ((346658711217 / 250000000000) : ℝ) = ((250000000000 / 346658711217) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0026 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_1664_neg : (32708523 / 100000000) ≤ -Real.log (500000000000 / 693459840077) ∧
    -Real.log (500000000000 / 693459840077) ≤ (327085231 / 1000000000) := by
  have h := checkLog_sound (w := (193459840077 / 1193459840077)) (n := 12)
    (lo := (32708523 / 100000000)) (hi := (327085231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693459840077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693459840077 / 500000000000) = 1/(500000000000 / 693459840077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1664 : Bounds (32708523 / 100000000) (327085231 / 1000000000) (Real.log (693459840077 / 500000000000)) := by
  have h := reflection_log_1664_neg
  have he : Real.log (693459840077 / 500000000000) = -Real.log (500000000000 / 693459840077) := by
    rw [show ((693459840077 / 500000000000) : ℝ) = ((500000000000 / 693459840077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1665_neg : (3757869 / 25000000) ≤ -Real.log (5000 / 5811) ∧
    -Real.log (5000 / 5811) ≤ (150314761 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 10811)) (n := 12)
    (lo := (3757869 / 25000000)) (hi := (150314761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5811 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5811 / 5000) = 1/(5000 / 5811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1665 : Bounds (3757869 / 25000000) (150314761 / 1000000000) (Real.log (5811 / 5000)) := by
  have h := reflection_log_1665_neg
  have he : Real.log (5811 / 5000) = -Real.log (5000 / 5811) := by
    rw [show ((5811 / 5000) : ℝ) = ((5000 / 5811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1666_neg : (17697587 / 100000000) ≤ -Real.log (4189 / 5000) ∧
    -Real.log (4189 / 5000) ≤ (176975871 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 9189)) (n := 12)
    (lo := (17697587 / 100000000)) (hi := (176975871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4189) = 1/(4189 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1666 : Bounds (-176975871 / 1000000000) (-17697587 / 100000000) (Real.log (4189 / 5000)) := by
  have h := reflection_log_1666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1667_neg : (81093 / 500000000) ≤ -Real.log (5000000 / 5000811) ∧
    -Real.log (5000000 / 5000811) ≤ (162187 / 1000000000) := by
  have h := checkLog_sound (w := (811 / 10000811)) (n := 12)
    (lo := (81093 / 500000000)) (hi := (162187 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000811 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000811 / 5000000) = 1/(5000000 / 5000811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1667 : Bounds (81093 / 500000000) (162187 / 1000000000) (Real.log (5000811 / 5000000)) := by
  have h := reflection_log_1667_neg
  have he : Real.log (5000811 / 5000000) = -Real.log (5000000 / 5000811) := by
    rw [show ((5000811 / 5000000) : ℝ) = ((5000000 / 5000811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1668_neg : (162213 / 1000000000) ≤ -Real.log (4999189 / 5000000) ∧
    -Real.log (4999189 / 5000000) ≤ (81107 / 500000000) := by
  have h := checkLog_sound (w := (811 / 9999189)) (n := 12)
    (lo := (162213 / 1000000000)) (hi := (81107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999189) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999189) = 1/(4999189 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1668 : Bounds (-81107 / 500000000) (-162213 / 1000000000) (Real.log (4999189 / 5000000)) := by
  have h := reflection_log_1668_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1669_neg : (78215809 / 1000000000) ≤ -Real.log (250000 / 270339) ∧
    -Real.log (250000 / 270339) ≤ (7821581 / 100000000) := by
  have h := checkLog_sound (w := (20339 / 520339)) (n := 12)
    (lo := (78215809 / 1000000000)) (hi := (7821581 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270339 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270339 / 250000) = 1/(250000 / 270339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1669 : Bounds (78215809 / 1000000000) (7821581 / 100000000) (Real.log (270339 / 250000)) := by
  have h := reflection_log_1669_neg
  have he : Real.log (270339 / 250000) = -Real.log (250000 / 270339) := by
    rw [show ((270339 / 250000) : ℝ) = ((250000 / 270339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1670_neg : (84856609 / 1000000000) ≤ -Real.log (229661 / 250000) ∧
    -Real.log (229661 / 250000) ≤ (8485661 / 100000000) := by
  have h := checkLog_sound (w := (20339 / 479661)) (n := 12)
    (lo := (84856609 / 1000000000)) (hi := (8485661 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229661) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229661) = 1/(229661 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1670 : Bounds (-8485661 / 100000000) (-84856609 / 1000000000) (Real.log (229661 / 250000)) := by
  have h := reflection_log_1670_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1671_neg : (19603191 / 250000000) ≤ -Real.log (1000000 / 1081569) ∧
    -Real.log (1000000 / 1081569) ≤ (15682553 / 200000000) := by
  have h := checkLog_sound (w := (81569 / 2081569)) (n := 12)
    (lo := (19603191 / 250000000)) (hi := (15682553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081569 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081569 / 1000000) = 1/(1000000 / 1081569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1671 : Bounds (19603191 / 250000000) (15682553 / 200000000) (Real.log (1081569 / 1000000)) := by
  have h := reflection_log_1671_neg
  have he : Real.log (1081569 / 1000000) = -Real.log (1000000 / 1081569) := by
    rw [show ((1081569 / 1000000) : ℝ) = ((1000000 / 1081569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1672_neg : (85088499 / 1000000000) ≤ -Real.log (918431 / 1000000) ∧
    -Real.log (918431 / 1000000) ≤ (170177 / 2000000) := by
  have h := checkLog_sound (w := (81569 / 1918431)) (n := 12)
    (lo := (85088499 / 1000000000)) (hi := (170177 / 2000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918431) = 1/(918431 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1672 : Bounds (-170177 / 2000000) (-85088499 / 1000000000) (Real.log (918431 / 1000000)) := by
  have h := reflection_log_1672_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1673_neg : (3337867 / 500000000) ≤ -Real.log (993346498239 / 1000000000000) ∧
    -Real.log (993346498239 / 1000000000000) ≤ (1335147 / 200000000) := by
  have h := checkLog_sound (w := (6653501761 / 1993346498239)) (n := 12)
    (lo := (3337867 / 500000000)) (hi := (1335147 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993346498239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993346498239) = 1/(993346498239 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1673 : Bounds (-1335147 / 200000000) (-3337867 / 500000000) (Real.log (993346498239 / 1000000000000)) := by
  have h := reflection_log_1673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1674_neg : (8301 / 1250000) ≤ -Real.log (62086325079 / 62500000000) ∧
    -Real.log (62086325079 / 62500000000) ≤ (6640801 / 1000000000) := by
  have h := checkLog_sound (w := (413674921 / 124586325079)) (n := 12)
    (lo := (8301 / 1250000)) (hi := (6640801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62086325079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62086325079) = 1/(62086325079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1674 : Bounds (-6640801 / 1000000000) (-8301 / 1250000) (Real.log (62086325079 / 62500000000)) := by
  have h := reflection_log_1674_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1675_neg : (81536209 / 500000000) ≤ -Real.log (100000000000 / 117712193189) ∧
    -Real.log (100000000000 / 117712193189) ≤ (163072419 / 1000000000) := by
  have h := checkLog_sound (w := (17712193189 / 217712193189)) (n := 12)
    (lo := (81536209 / 500000000)) (hi := (163072419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((117712193189 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(117712193189 / 100000000000) = 1/(100000000000 / 117712193189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1675 : Bounds (81536209 / 500000000) (163072419 / 1000000000) (Real.log (117712193189 / 100000000000)) := by
  have h := reflection_log_1675_neg
  have he : Real.log (117712193189 / 100000000000) = -Real.log (100000000000 / 117712193189) := by
    rw [show ((117712193189 / 100000000000) : ℝ) = ((100000000000 / 117712193189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1676_neg : (10218829 / 62500000) ≤ -Real.log (500000000000 / 588813422021) ∧
    -Real.log (500000000000 / 588813422021) ≤ (32700253 / 200000000) := by
  have h := checkLog_sound (w := (88813422021 / 1088813422021)) (n := 12)
    (lo := (10218829 / 62500000)) (hi := (32700253 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588813422021 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588813422021 / 500000000000) = 1/(500000000000 / 588813422021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1676 : Bounds (10218829 / 62500000) (32700253 / 200000000) (Real.log (588813422021 / 500000000000)) := by
  have h := reflection_log_1676_neg
  have he : Real.log (588813422021 / 500000000000) = -Real.log (500000000000 / 588813422021) := by
    rw [show ((588813422021 / 500000000000) : ℝ) = ((500000000000 / 588813422021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1677_neg : (32708523 / 100000000) ≤ -Real.log (125000000000 / 173364960019) ∧
    -Real.log (125000000000 / 173364960019) ≤ (327085231 / 1000000000) := by
  have h := checkLog_sound (w := (48364960019 / 298364960019)) (n := 12)
    (lo := (32708523 / 100000000)) (hi := (327085231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173364960019 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173364960019 / 125000000000) = 1/(125000000000 / 173364960019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1677 : Bounds (32708523 / 100000000) (327085231 / 1000000000) (Real.log (173364960019 / 125000000000)) := by
  have h := reflection_log_1677_neg
  have he : Real.log (173364960019 / 125000000000) = -Real.log (125000000000 / 173364960019) := by
    rw [show ((173364960019 / 125000000000) : ℝ) = ((125000000000 / 173364960019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1678_neg : (327290631 / 1000000000) ≤ -Real.log (500000000000 / 693602291717) ∧
    -Real.log (500000000000 / 693602291717) ≤ (40911329 / 125000000) := by
  have h := checkLog_sound (w := (193602291717 / 1193602291717)) (n := 12)
    (lo := (327290631 / 1000000000)) (hi := (40911329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693602291717 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693602291717 / 500000000000) = 1/(500000000000 / 693602291717) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1678 : Bounds (327290631 / 1000000000) (40911329 / 125000000) (Real.log (693602291717 / 500000000000)) := by
  have h := reflection_log_1678_neg
  have he : Real.log (693602291717 / 500000000000) = -Real.log (500000000000 / 693602291717) := by
    rw [show ((693602291717 / 500000000000) : ℝ) = ((500000000000 / 693602291717) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1679_neg : (188001 / 1250000) ≤ -Real.log (10000 / 11623) ∧
    -Real.log (10000 / 11623) ≤ (150400801 / 1000000000) := by
  have h := checkLog_sound (w := (1623 / 21623)) (n := 12)
    (lo := (188001 / 1250000)) (hi := (150400801 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11623 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11623 / 10000) = 1/(10000 / 11623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1679 : Bounds (188001 / 1250000) (150400801 / 1000000000) (Real.log (11623 / 10000)) := by
  have h := reflection_log_1679_neg
  have he : Real.log (11623 / 10000) = -Real.log (10000 / 11623) := by
    rw [show ((11623 / 10000) : ℝ) = ((10000 / 11623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1680_neg : (177095237 / 1000000000) ≤ -Real.log (8377 / 10000) ∧
    -Real.log (8377 / 10000) ≤ (88547619 / 500000000) := by
  have h := checkLog_sound (w := (1623 / 18377)) (n := 12)
    (lo := (177095237 / 1000000000)) (hi := (88547619 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8377) = 1/(8377 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1680 : Bounds (-88547619 / 500000000) (-177095237 / 1000000000) (Real.log (8377 / 10000)) := by
  have h := reflection_log_1680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1681_neg : (81143 / 500000000) ≤ -Real.log (10000000 / 10001623) ∧
    -Real.log (10000000 / 10001623) ≤ (162287 / 1000000000) := by
  have h := checkLog_sound (w := (1623 / 20001623)) (n := 12)
    (lo := (81143 / 500000000)) (hi := (162287 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001623 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001623 / 10000000) = 1/(10000000 / 10001623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1681 : Bounds (81143 / 500000000) (162287 / 1000000000) (Real.log (10001623 / 10000000)) := by
  have h := reflection_log_1681_neg
  have he : Real.log (10001623 / 10000000) = -Real.log (10000000 / 10001623) := by
    rw [show ((10001623 / 10000000) : ℝ) = ((10000000 / 10001623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1682_neg : (162313 / 1000000000) ≤ -Real.log (9998377 / 10000000) ∧
    -Real.log (9998377 / 10000000) ≤ (81157 / 500000000) := by
  have h := checkLog_sound (w := (1623 / 19998377)) (n := 12)
    (lo := (162313 / 1000000000)) (hi := (81157 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998377) = 1/(9998377 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1682 : Bounds (-81157 / 500000000) (-162313 / 1000000000) (Real.log (9998377 / 10000000)) := by
  have h := reflection_log_1682_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1683_neg : (78262971 / 1000000000) ≤ -Real.log (1000000 / 1081407) ∧
    -Real.log (1000000 / 1081407) ≤ (19565743 / 250000000) := by
  have h := checkLog_sound (w := (81407 / 2081407)) (n := 12)
    (lo := (78262971 / 1000000000)) (hi := (19565743 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081407 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081407 / 1000000) = 1/(1000000 / 1081407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1683 : Bounds (78262971 / 1000000000) (19565743 / 250000000) (Real.log (1081407 / 1000000)) := by
  have h := reflection_log_1683_neg
  have he : Real.log (1081407 / 1000000) = -Real.log (1000000 / 1081407) := by
    rw [show ((1081407 / 1000000) : ℝ) = ((1000000 / 1081407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1684_neg : (84912127 / 1000000000) ≤ -Real.log (918593 / 1000000) ∧
    -Real.log (918593 / 1000000) ≤ (165844 / 1953125) := by
  have h := checkLog_sound (w := (81407 / 1918593)) (n := 12)
    (lo := (84912127 / 1000000000)) (hi := (165844 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918593) = 1/(918593 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1684 : Bounds (-165844 / 1953125) (-84912127 / 1000000000) (Real.log (918593 / 1000000)) := by
  have h := reflection_log_1684_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1685_neg : (78459917 / 1000000000) ≤ -Real.log (50000 / 54081) ∧
    -Real.log (50000 / 54081) ≤ (39229959 / 500000000) := by
  have h := checkLog_sound (w := (4081 / 104081)) (n := 12)
    (lo := (78459917 / 1000000000)) (hi := (39229959 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((54081 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(54081 / 50000) = 1/(50000 / 54081) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1685 : Bounds (78459917 / 1000000000) (39229959 / 500000000) (Real.log (54081 / 50000)) := by
  have h := reflection_log_1685_neg
  have he : Real.log (54081 / 50000) = -Real.log (50000 / 54081) := by
    rw [show ((54081 / 50000) : ℝ) = ((50000 / 54081) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1686_neg : (8514403 / 100000000) ≤ -Real.log (45919 / 50000) ∧
    -Real.log (45919 / 50000) ≤ (85144031 / 1000000000) := by
  have h := checkLog_sound (w := (4081 / 95919)) (n := 12)
    (lo := (8514403 / 100000000)) (hi := (85144031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 45919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 45919) = 1/(45919 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1686 : Bounds (-85144031 / 1000000000) (-8514403 / 100000000) (Real.log (45919 / 50000)) := by
  have h := reflection_log_1686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1687_neg : (6684113 / 1000000000) ≤ -Real.log (2483345439 / 2500000000) ∧
    -Real.log (2483345439 / 2500000000) ≤ (3342057 / 500000000) := by
  have h := checkLog_sound (w := (16654561 / 4983345439)) (n := 12)
    (lo := (6684113 / 1000000000)) (hi := (3342057 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000000 / 2483345439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000000 / 2483345439) = 1/(2483345439 / 2500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1687 : Bounds (-3342057 / 500000000) (-6684113 / 1000000000) (Real.log (2483345439 / 2500000000)) := by
  have h := reflection_log_1687_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1688_neg : (1662289 / 250000000) ≤ -Real.log (993372900351 / 1000000000000) ∧
    -Real.log (993372900351 / 1000000000000) ≤ (6649157 / 1000000000) := by
  have h := checkLog_sound (w := (6627099649 / 1993372900351)) (n := 12)
    (lo := (1662289 / 250000000)) (hi := (6649157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993372900351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993372900351) = 1/(993372900351 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1688 : Bounds (-6649157 / 1000000000) (-1662289 / 250000000) (Real.log (993372900351 / 1000000000000)) := by
  have h := reflection_log_1688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1689_neg : (81587549 / 500000000) ≤ -Real.log (250000000000 / 294310701257) ∧
    -Real.log (250000000000 / 294310701257) ≤ (163175099 / 1000000000) := by
  have h := checkLog_sound (w := (44310701257 / 544310701257)) (n := 12)
    (lo := (81587549 / 500000000)) (hi := (163175099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((294310701257 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(294310701257 / 250000000000) = 1/(250000000000 / 294310701257) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1689 : Bounds (81587549 / 500000000) (163175099 / 1000000000) (Real.log (294310701257 / 250000000000)) := by
  have h := reflection_log_1689_neg
  have he : Real.log (294310701257 / 250000000000) = -Real.log (250000000000 / 294310701257) := by
    rw [show ((294310701257 / 250000000000) : ℝ) = ((250000000000 / 294310701257) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1690_neg : (163603947 / 1000000000) ≤ -Real.log (500000000000 / 588873886627) ∧
    -Real.log (500000000000 / 588873886627) ≤ (40900987 / 250000000) := by
  have h := checkLog_sound (w := (88873886627 / 1088873886627)) (n := 12)
    (lo := (163603947 / 1000000000)) (hi := (40900987 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588873886627 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588873886627 / 500000000000) = 1/(500000000000 / 588873886627) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1690 : Bounds (163603947 / 1000000000) (40900987 / 250000000) (Real.log (588873886627 / 500000000000)) := by
  have h := reflection_log_1690_neg
  have he : Real.log (588873886627 / 500000000000) = -Real.log (500000000000 / 588873886627) := by
    rw [show ((588873886627 / 500000000000) : ℝ) = ((500000000000 / 588873886627) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1691_neg : (327290631 / 1000000000) ≤ -Real.log (125000000000 / 173400572929) ∧
    -Real.log (125000000000 / 173400572929) ≤ (40911329 / 125000000) := by
  have h := checkLog_sound (w := (48400572929 / 298400572929)) (n := 12)
    (lo := (327290631 / 1000000000)) (hi := (40911329 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((173400572929 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(173400572929 / 125000000000) = 1/(125000000000 / 173400572929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1691 : Bounds (327290631 / 1000000000) (40911329 / 125000000) (Real.log (173400572929 / 125000000000)) := by
  have h := reflection_log_1691_neg
  have he : Real.log (173400572929 / 125000000000) = -Real.log (125000000000 / 173400572929) := by
    rw [show ((173400572929 / 125000000000) : ℝ) = ((125000000000 / 173400572929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1692_neg : (163748019 / 500000000) ≤ -Real.log (500000000000 / 693744777367) ∧
    -Real.log (500000000000 / 693744777367) ≤ (327496039 / 1000000000) := by
  have h := checkLog_sound (w := (193744777367 / 1193744777367)) (n := 12)
    (lo := (163748019 / 500000000)) (hi := (327496039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693744777367 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693744777367 / 500000000000) = 1/(500000000000 / 693744777367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1692 : Bounds (163748019 / 500000000) (327496039 / 1000000000) (Real.log (693744777367 / 500000000000)) := by
  have h := reflection_log_1692_neg
  have he : Real.log (693744777367 / 500000000000) = -Real.log (500000000000 / 693744777367) := by
    rw [show ((693744777367 / 500000000000) : ℝ) = ((500000000000 / 693744777367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1693_neg : (150486833 / 1000000000) ≤ -Real.log (1250 / 1453) ∧
    -Real.log (1250 / 1453) ≤ (75243417 / 500000000) := by
  have h := checkLog_sound (w := (203 / 2703)) (n := 12)
    (lo := (150486833 / 1000000000)) (hi := (75243417 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1453 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1453 / 1250) = 1/(1250 / 1453) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1693 : Bounds (150486833 / 1000000000) (75243417 / 500000000) (Real.log (1453 / 1250)) := by
  have h := reflection_log_1693_neg
  have he : Real.log (1453 / 1250) = -Real.log (1250 / 1453) := by
    rw [show ((1453 / 1250) : ℝ) = ((1250 / 1453) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1694_neg : (177214619 / 1000000000) ≤ -Real.log (1047 / 1250) ∧
    -Real.log (1047 / 1250) ≤ (8860731 / 50000000) := by
  have h := checkLog_sound (w := (203 / 2297)) (n := 12)
    (lo := (177214619 / 1000000000)) (hi := (8860731 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250 / 1047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250 / 1047) = 1/(1047 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1694 : Bounds (-8860731 / 50000000) (-177214619 / 1000000000) (Real.log (1047 / 1250)) := by
  have h := reflection_log_1694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1695_neg : (81193 / 500000000) ≤ -Real.log (1250000 / 1250203) ∧
    -Real.log (1250000 / 1250203) ≤ (162387 / 1000000000) := by
  have h := checkLog_sound (w := (203 / 2500203)) (n := 12)
    (lo := (81193 / 500000000)) (hi := (162387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250203 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250203 / 1250000) = 1/(1250000 / 1250203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1695 : Bounds (81193 / 500000000) (162387 / 1000000000) (Real.log (1250203 / 1250000)) := by
  have h := reflection_log_1695_neg
  have he : Real.log (1250203 / 1250000) = -Real.log (1250000 / 1250203) := by
    rw [show ((1250203 / 1250000) : ℝ) = ((1250000 / 1250203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1696_neg : (162413 / 1000000000) ≤ -Real.log (1249797 / 1250000) ∧
    -Real.log (1249797 / 1250000) ≤ (81207 / 500000000) := by
  have h := checkLog_sound (w := (203 / 2499797)) (n := 12)
    (lo := (162413 / 1000000000)) (hi := (81207 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1249797) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1249797) = 1/(1249797 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1696 : Bounds (-81207 / 500000000) (-162413 / 1000000000) (Real.log (1249797 / 1250000)) := by
  have h := reflection_log_1696_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1697_neg : (39154603 / 500000000) ≤ -Real.log (1000000 / 1081457) ∧
    -Real.log (1000000 / 1081457) ≤ (78309207 / 1000000000) := by
  have h := checkLog_sound (w := (81457 / 2081457)) (n := 12)
    (lo := (39154603 / 500000000)) (hi := (78309207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081457 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081457 / 1000000) = 1/(1000000 / 1081457) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1697 : Bounds (39154603 / 500000000) (78309207 / 1000000000) (Real.log (1081457 / 1000000)) := by
  have h := reflection_log_1697_neg
  have he : Real.log (1081457 / 1000000) = -Real.log (1000000 / 1081457) := by
    rw [show ((1081457 / 1000000) : ℝ) = ((1000000 / 1081457) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1698_neg : (84966559 / 1000000000) ≤ -Real.log (918543 / 1000000) ∧
    -Real.log (918543 / 1000000) ≤ (531041 / 6250000) := by
  have h := checkLog_sound (w := (81457 / 1918543)) (n := 12)
    (lo := (84966559 / 1000000000)) (hi := (531041 / 6250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918543) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918543) = 1/(918543 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1698 : Bounds (-531041 / 6250000) (-84966559 / 1000000000) (Real.log (918543 / 1000000)) := by
  have h := reflection_log_1698_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1699_neg : (78507067 / 1000000000) ≤ -Real.log (1000000 / 1081671) ∧
    -Real.log (1000000 / 1081671) ≤ (19626767 / 250000000) := by
  have h := checkLog_sound (w := (81671 / 2081671)) (n := 12)
    (lo := (78507067 / 1000000000)) (hi := (19626767 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081671 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081671 / 1000000) = 1/(1000000 / 1081671) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1699 : Bounds (78507067 / 1000000000) (19626767 / 250000000) (Real.log (1081671 / 1000000)) := by
  have h := reflection_log_1699_neg
  have he : Real.log (1081671 / 1000000) = -Real.log (1000000 / 1081671) := by
    rw [show ((1081671 / 1000000) : ℝ) = ((1000000 / 1081671) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1700_neg : (21299891 / 250000000) ≤ -Real.log (918329 / 1000000) ∧
    -Real.log (918329 / 1000000) ≤ (17039913 / 200000000) := by
  have h := checkLog_sound (w := (81671 / 1918329)) (n := 12)
    (lo := (21299891 / 250000000)) (hi := (17039913 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918329) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918329) = 1/(918329 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1700 : Bounds (-17039913 / 200000000) (-21299891 / 250000000) (Real.log (918329 / 1000000)) := by
  have h := reflection_log_1700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1701_neg : (6692497 / 1000000000) ≤ -Real.log (993329847759 / 1000000000000) ∧
    -Real.log (993329847759 / 1000000000000) ≤ (3346249 / 500000000) := by
  have h := checkLog_sound (w := (6670152241 / 1993329847759)) (n := 12)
    (lo := (6692497 / 1000000000)) (hi := (3346249 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993329847759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993329847759) = 1/(993329847759 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1701 : Bounds (-3346249 / 500000000) (-6692497 / 1000000000) (Real.log (993329847759 / 1000000000000)) := by
  have h := reflection_log_1701_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1702_neg : (6657353 / 1000000000) ≤ -Real.log (993364757151 / 1000000000000) ∧
    -Real.log (993364757151 / 1000000000000) ≤ (3328677 / 500000000) := by
  have h := checkLog_sound (w := (6635242849 / 1993364757151)) (n := 12)
    (lo := (6657353 / 1000000000)) (hi := (3328677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993364757151) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993364757151) = 1/(993364757151 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1702 : Bounds (-3328677 / 500000000) (-6657353 / 1000000000) (Real.log (993364757151 / 1000000000000)) := by
  have h := reflection_log_1702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1703_neg : (32655153 / 200000000) ≤ -Real.log (500000000000 / 588680660567) ∧
    -Real.log (500000000000 / 588680660567) ≤ (81637883 / 500000000) := by
  have h := checkLog_sound (w := (88680660567 / 1088680660567)) (n := 12)
    (lo := (32655153 / 200000000)) (hi := (81637883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588680660567 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588680660567 / 500000000000) = 1/(500000000000 / 588680660567) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1703 : Bounds (32655153 / 200000000) (81637883 / 500000000) (Real.log (588680660567 / 500000000000)) := by
  have h := reflection_log_1703_neg
  have he : Real.log (588680660567 / 500000000000) = -Real.log (500000000000 / 588680660567) := by
    rw [show ((588680660567 / 500000000000) : ℝ) = ((500000000000 / 588680660567) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1704_neg : (20463329 / 125000000) ≤ -Real.log (125000000000 / 147233589487) ∧
    -Real.log (125000000000 / 147233589487) ≤ (163706633 / 1000000000) := by
  have h := checkLog_sound (w := (22233589487 / 272233589487)) (n := 12)
    (lo := (20463329 / 125000000)) (hi := (163706633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147233589487 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147233589487 / 125000000000) = 1/(125000000000 / 147233589487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1704 : Bounds (20463329 / 125000000) (163706633 / 1000000000) (Real.log (147233589487 / 125000000000)) := by
  have h := reflection_log_1704_neg
  have he : Real.log (147233589487 / 125000000000) = -Real.log (125000000000 / 147233589487) := by
    rw [show ((147233589487 / 125000000000) : ℝ) = ((125000000000 / 147233589487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1705_neg : (163748019 / 500000000) ≤ -Real.log (250000000000 / 346872388683) ∧
    -Real.log (250000000000 / 346872388683) ≤ (327496039 / 1000000000) := by
  have h := checkLog_sound (w := (96872388683 / 596872388683)) (n := 12)
    (lo := (163748019 / 500000000)) (hi := (327496039 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((346872388683 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(346872388683 / 250000000000) = 1/(250000000000 / 346872388683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1705 : Bounds (163748019 / 500000000) (327496039 / 1000000000) (Real.log (346872388683 / 250000000000)) := by
  have h := reflection_log_1705_neg
  have he : Real.log (346872388683 / 250000000000) = -Real.log (250000000000 / 346872388683) := by
    rw [show ((346872388683 / 250000000000) : ℝ) = ((250000000000 / 346872388683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1706_neg : (81925363 / 250000000) ≤ -Real.log (6250000000 / 8673591213) ∧
    -Real.log (6250000000 / 8673591213) ≤ (327701453 / 1000000000) := by
  have h := checkLog_sound (w := (2423591213 / 14923591213)) (n := 12)
    (lo := (81925363 / 250000000)) (hi := (327701453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8673591213 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(8673591213 / 6250000000) = 1/(6250000000 / 8673591213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1706 : Bounds (81925363 / 250000000) (327701453 / 1000000000) (Real.log (8673591213 / 6250000000)) := by
  have h := reflection_log_1706_neg
  have he : Real.log (8673591213 / 6250000000) = -Real.log (6250000000 / 8673591213) := by
    rw [show ((8673591213 / 6250000000) : ℝ) = ((6250000000 / 8673591213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1707_neg : (75286429 / 500000000) ≤ -Real.log (80 / 93) ∧
    -Real.log (80 / 93) ≤ (150572859 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 173)) (n := 12)
    (lo := (75286429 / 500000000)) (hi := (150572859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((93 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(93 / 80) = 1/(80 / 93) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1707 : Bounds (75286429 / 500000000) (150572859 / 1000000000) (Real.log (93 / 80)) := by
  have h := reflection_log_1707_neg
  have he : Real.log (93 / 80) = -Real.log (80 / 93) := by
    rw [show ((93 / 80) : ℝ) = ((80 / 93) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1708_neg : (35466803 / 200000000) ≤ -Real.log (67 / 80) ∧
    -Real.log (67 / 80) ≤ (692711 / 3906250) := by
  have h := checkLog_sound (w := (13 / 147)) (n := 12)
    (lo := (35466803 / 200000000)) (hi := (692711 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 67) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 67) = 1/(67 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1708 : Bounds (-692711 / 3906250) (-35466803 / 200000000) (Real.log (67 / 80)) := by
  have h := reflection_log_1708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1709_neg : (81243 / 500000000) ≤ -Real.log (80000 / 80013) ∧
    -Real.log (80000 / 80013) ≤ (162487 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 160013)) (n := 12)
    (lo := (81243 / 500000000)) (hi := (162487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80013 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80013 / 80000) = 1/(80000 / 80013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1709 : Bounds (81243 / 500000000) (162487 / 1000000000) (Real.log (80013 / 80000)) := by
  have h := reflection_log_1709_neg
  have he : Real.log (80013 / 80000) = -Real.log (80000 / 80013) := by
    rw [show ((80013 / 80000) : ℝ) = ((80000 / 80013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1710_neg : (162513 / 1000000000) ≤ -Real.log (79987 / 80000) ∧
    -Real.log (79987 / 80000) ≤ (81257 / 500000000) := by
  have h := checkLog_sound (w := (13 / 159987)) (n := 12)
    (lo := (162513 / 1000000000)) (hi := (81257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79987) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79987) = 1/(79987 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1710 : Bounds (-81257 / 500000000) (-162513 / 1000000000) (Real.log (79987 / 80000)) := by
  have h := reflection_log_1710_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1711_neg : (78356363 / 1000000000) ≤ -Real.log (250000 / 270377) ∧
    -Real.log (250000 / 270377) ≤ (19589091 / 250000000) := by
  have h := checkLog_sound (w := (20377 / 520377)) (n := 12)
    (lo := (78356363 / 1000000000)) (hi := (19589091 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270377 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270377 / 250000) = 1/(250000 / 270377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1711 : Bounds (78356363 / 1000000000) (19589091 / 250000000) (Real.log (270377 / 250000)) := by
  have h := reflection_log_1711_neg
  have he : Real.log (270377 / 250000) = -Real.log (250000 / 270377) := by
    rw [show ((270377 / 250000) : ℝ) = ((250000 / 270377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1712_neg : (21255521 / 250000000) ≤ -Real.log (229623 / 250000) ∧
    -Real.log (229623 / 250000) ≤ (17004417 / 200000000) := by
  have h := checkLog_sound (w := (20377 / 479623)) (n := 12)
    (lo := (21255521 / 250000000)) (hi := (17004417 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 229623) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 229623) = 1/(229623 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1712 : Bounds (-17004417 / 200000000) (-21255521 / 250000000) (Real.log (229623 / 250000)) := by
  have h := reflection_log_1712_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1713_neg : (78553291 / 1000000000) ≤ -Real.log (1000000 / 1081721) ∧
    -Real.log (1000000 / 1081721) ≤ (19638323 / 250000000) := by
  have h := checkLog_sound (w := (81721 / 2081721)) (n := 12)
    (lo := (78553291 / 1000000000)) (hi := (19638323 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081721 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081721 / 1000000) = 1/(1000000 / 1081721) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1713 : Bounds (78553291 / 1000000000) (19638323 / 250000000) (Real.log (1081721 / 1000000)) := by
  have h := reflection_log_1713_neg
  have he : Real.log (1081721 / 1000000) = -Real.log (1000000 / 1081721) := by
    rw [show ((1081721 / 1000000) : ℝ) = ((1000000 / 1081721) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1714_neg : (21313503 / 250000000) ≤ -Real.log (918279 / 1000000) ∧
    -Real.log (918279 / 1000000) ≤ (85254013 / 1000000000) := by
  have h := checkLog_sound (w := (81721 / 1918279)) (n := 12)
    (lo := (21313503 / 250000000)) (hi := (85254013 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918279) = 1/(918279 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1714 : Bounds (-85254013 / 1000000000) (-21313503 / 250000000) (Real.log (918279 / 1000000)) := by
  have h := reflection_log_1714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1715_neg : (6700721 / 1000000000) ≤ -Real.log (993321678159 / 1000000000000) ∧
    -Real.log (993321678159 / 1000000000000) ≤ (3350361 / 500000000) := by
  have h := checkLog_sound (w := (6678321841 / 1993321678159)) (n := 12)
    (lo := (6700721 / 1000000000)) (hi := (3350361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 993321678159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 993321678159) = 1/(993321678159 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1715 : Bounds (-3350361 / 500000000) (-6700721 / 1000000000) (Real.log (993321678159 / 1000000000000)) := by
  have h := reflection_log_1715_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1716_neg : (166643 / 25000000) ≤ -Real.log (62084777871 / 62500000000) ∧
    -Real.log (62084777871 / 62500000000) ≤ (6665721 / 1000000000) := by
  have h := checkLog_sound (w := (415222129 / 124584777871)) (n := 12)
    (lo := (166643 / 25000000)) (hi := (6665721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 62084777871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 62084777871) = 1/(62084777871 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1716 : Bounds (-6665721 / 1000000000) (-166643 / 25000000) (Real.log (62084777871 / 62500000000)) := by
  have h := reflection_log_1716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1717_neg : (163378447 / 1000000000) ≤ -Real.log (125000000000 / 147185277607) ∧
    -Real.log (125000000000 / 147185277607) ≤ (10211153 / 62500000) := by
  have h := checkLog_sound (w := (22185277607 / 272185277607)) (n := 12)
    (lo := (163378447 / 1000000000)) (hi := (10211153 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147185277607 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147185277607 / 125000000000) = 1/(125000000000 / 147185277607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1717 : Bounds (163378447 / 1000000000) (10211153 / 62500000) (Real.log (147185277607 / 125000000000)) := by
  have h := reflection_log_1717_neg
  have he : Real.log (147185277607 / 125000000000) = -Real.log (125000000000 / 147185277607) := by
    rw [show ((147185277607 / 125000000000) : ℝ) = ((125000000000 / 147185277607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1718_neg : (20475913 / 125000000) ≤ -Real.log (500000000000 / 588993650079) ∧
    -Real.log (500000000000 / 588993650079) ≤ (32761461 / 200000000) := by
  have h := checkLog_sound (w := (88993650079 / 1088993650079)) (n := 12)
    (lo := (20475913 / 125000000)) (hi := (32761461 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((588993650079 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(588993650079 / 500000000000) = 1/(500000000000 / 588993650079) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1718 : Bounds (20475913 / 125000000) (32761461 / 200000000) (Real.log (588993650079 / 500000000000)) := by
  have h := reflection_log_1718_neg
  have he : Real.log (588993650079 / 500000000000) = -Real.log (500000000000 / 588993650079) := by
    rw [show ((588993650079 / 500000000000) : ℝ) = ((500000000000 / 588993650079) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1719_neg : (81925363 / 250000000) ≤ -Real.log (500000000000 / 693887297039) ∧
    -Real.log (500000000000 / 693887297039) ≤ (327701453 / 1000000000) := by
  have h := checkLog_sound (w := (193887297039 / 1193887297039)) (n := 12)
    (lo := (81925363 / 250000000)) (hi := (327701453 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((693887297039 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(693887297039 / 500000000000) = 1/(500000000000 / 693887297039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1719 : Bounds (81925363 / 250000000) (327701453 / 1000000000) (Real.log (693887297039 / 500000000000)) := by
  have h := reflection_log_1719_neg
  have he : Real.log (693887297039 / 500000000000) = -Real.log (500000000000 / 693887297039) := by
    rw [show ((693887297039 / 500000000000) : ℝ) = ((500000000000 / 693887297039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1720_neg : (327906873 / 1000000000) ≤ -Real.log (500000000000 / 694029850747) ∧
    -Real.log (500000000000 / 694029850747) ≤ (163953437 / 500000000) := by
  have h := checkLog_sound (w := (194029850747 / 1194029850747)) (n := 12)
    (lo := (327906873 / 1000000000)) (hi := (163953437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((694029850747 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(694029850747 / 500000000000) = 1/(500000000000 / 694029850747) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1720 : Bounds (327906873 / 1000000000) (163953437 / 500000000) (Real.log (694029850747 / 500000000000)) := by
  have h := reflection_log_1720_neg
  have he : Real.log (694029850747 / 500000000000) = -Real.log (500000000000 / 694029850747) := by
    rw [show ((694029850747 / 500000000000) : ℝ) = ((500000000000 / 694029850747) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1721_neg : (37664719 / 250000000) ≤ -Real.log (5000 / 5813) ∧
    -Real.log (5000 / 5813) ≤ (150658877 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 10813)) (n := 12)
    (lo := (37664719 / 250000000)) (hi := (150658877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5813 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5813 / 5000) = 1/(5000 / 5813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1721 : Bounds (37664719 / 250000000) (150658877 / 1000000000) (Real.log (5813 / 5000)) := by
  have h := reflection_log_1721_neg
  have he : Real.log (5813 / 5000) = -Real.log (5000 / 5813) := by
    rw [show ((5813 / 5000) : ℝ) = ((5000 / 5813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1722_neg : (7098137 / 40000000) ≤ -Real.log (4187 / 5000) ∧
    -Real.log (4187 / 5000) ≤ (88726713 / 500000000) := by
  have h := checkLog_sound (w := (813 / 9187)) (n := 12)
    (lo := (7098137 / 40000000)) (hi := (88726713 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4187) = 1/(4187 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1722 : Bounds (-88726713 / 500000000) (-7098137 / 40000000) (Real.log (4187 / 5000)) := by
  have h := reflection_log_1722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1723_neg : (81293 / 500000000) ≤ -Real.log (5000000 / 5000813) ∧
    -Real.log (5000000 / 5000813) ≤ (162587 / 1000000000) := by
  have h := checkLog_sound (w := (813 / 10000813)) (n := 12)
    (lo := (81293 / 500000000)) (hi := (162587 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000813 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000813 / 5000000) = 1/(5000000 / 5000813) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1723 : Bounds (81293 / 500000000) (162587 / 1000000000) (Real.log (5000813 / 5000000)) := by
  have h := reflection_log_1723_neg
  have he : Real.log (5000813 / 5000000) = -Real.log (5000000 / 5000813) := by
    rw [show ((5000813 / 5000000) : ℝ) = ((5000000 / 5000813) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1724_neg : (162613 / 1000000000) ≤ -Real.log (4999187 / 5000000) ∧
    -Real.log (4999187 / 5000000) ≤ (81307 / 500000000) := by
  have h := checkLog_sound (w := (813 / 9999187)) (n := 12)
    (lo := (162613 / 1000000000)) (hi := (81307 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999187) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999187) = 1/(4999187 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1724 : Bounds (-81307 / 500000000) (-162613 / 1000000000) (Real.log (4999187 / 5000000)) := by
  have h := reflection_log_1724_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1725_neg : (39201759 / 500000000) ≤ -Real.log (1000000 / 1081559) ∧
    -Real.log (1000000 / 1081559) ≤ (78403519 / 1000000000) := by
  have h := checkLog_sound (w := (81559 / 2081559)) (n := 12)
    (lo := (39201759 / 500000000)) (hi := (78403519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1081559 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1081559 / 1000000) = 1/(1000000 / 1081559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1725 : Bounds (39201759 / 500000000) (78403519 / 1000000000) (Real.log (1081559 / 1000000)) := by
  have h := reflection_log_1725_neg
  have he : Real.log (1081559 / 1000000) = -Real.log (1000000 / 1081559) := by
    rw [show ((1081559 / 1000000) : ℝ) = ((1000000 / 1081559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_1726_neg : (85077611 / 1000000000) ≤ -Real.log (918441 / 1000000) ∧
    -Real.log (918441 / 1000000) ≤ (21269403 / 250000000) := by
  have h := checkLog_sound (w := (81559 / 1918441)) (n := 12)
    (lo := (85077611 / 1000000000)) (hi := (21269403 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 918441) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 918441) = 1/(918441 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1726 : Bounds (-21269403 / 250000000) (-85077611 / 1000000000) (Real.log (918441 / 1000000)) := by
  have h := reflection_log_1726_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_1727_neg : (78600437 / 1000000000) ≤ -Real.log (250000 / 270443) ∧
    -Real.log (250000 / 270443) ≤ (39300219 / 500000000) := by
  have h := checkLog_sound (w := (20443 / 520443)) (n := 12)
    (lo := (78600437 / 1000000000)) (hi := (39300219 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((270443 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(270443 / 250000) = 1/(250000 / 270443) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_1727 : Bounds (78600437 / 1000000000) (39300219 / 500000000) (Real.log (270443 / 250000)) := by
  have h := reflection_log_1727_neg
  have he : Real.log (270443 / 250000) = -Real.log (250000 / 270443) := by
    rw [show ((270443 / 250000) : ℝ) = ((250000 / 270443) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


