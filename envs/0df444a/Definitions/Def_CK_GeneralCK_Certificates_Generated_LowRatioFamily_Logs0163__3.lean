-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0163__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0163__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T01:41:31.885778+00:00
-- url     : https://prove2.me/theorems/14f7d9ca-741b-4ccf-bd68-eb084e39a3d0
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0163 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0164, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0163 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0164, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0165)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0163 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0164, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0165)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0163 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0164, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0165) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0163 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0164, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0165).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0163 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10432_neg : (360064303 / 1000000000) ≤ -Real.log (62500000000 / 89588849089) ∧
    -Real.log (62500000000 / 89588849089) ≤ (22504019 / 62500000) := by
  have h := checkLog_sound (w := (27088849089 / 152088849089)) (n := 12)
    (lo := (360064303 / 1000000000)) (hi := (22504019 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89588849089 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89588849089 / 62500000000) = 1/(62500000000 / 89588849089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10432 : Bounds (360064303 / 1000000000) (22504019 / 62500000) (Real.log (89588849089 / 62500000000)) := by
  have h := reflection_log_10432_neg
  have he : Real.log (89588849089 / 62500000000) = -Real.log (62500000000 / 89588849089) := by
    rw [show ((89588849089 / 62500000000) : ℝ) = ((62500000000 / 89588849089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10433_neg : (362029023 / 500000000) ≤ -Real.log (500000000000 / 1031393568147) ∧
    -Real.log (500000000000 / 1031393568147) ≤ (11313407 / 15625000) := by
  have h := checkLog_sound (w := (31393568147 / 2031393568147)) (n := 12)
    (lo := (15455433 / 500000000)) (hi := (30910867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1031393568147 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1031393568147 / 1000000000000) = 1/(500000000000 / 1031393568147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10433 : Bounds (362029023 / 500000000) (11313407 / 15625000) (Real.log (1031393568147 / 500000000000)) := by
  have h := reflection_log_10433_neg
  have he : Real.log (1031393568147 / 500000000000) = -Real.log (500000000000 / 1031393568147) := by
    rw [show ((1031393568147 / 500000000000) : ℝ) = ((500000000000 / 1031393568147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10434_neg : (90791591 / 125000000) ≤ -Real.log (500000000000 / 1033742331289) ∧
    -Real.log (500000000000 / 1033742331289) ≤ (72633273 / 100000000) := by
  have h := checkLog_sound (w := (33742331289 / 2033742331289)) (n := 12)
    (lo := (8296387 / 250000000)) (hi := (33185549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1033742331289 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1033742331289 / 1000000000000) = 1/(500000000000 / 1033742331289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10434 : Bounds (90791591 / 125000000) (72633273 / 100000000) (Real.log (1033742331289 / 500000000000)) := by
  have h := reflection_log_10434_neg
  have he : Real.log (1033742331289 / 500000000000) = -Real.log (500000000000 / 1033742331289) := by
    rw [show ((1033742331289 / 500000000000) : ℝ) = ((500000000000 / 1033742331289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10435_neg : (299363577 / 1000000000) ≤ -Real.log (1000 / 1349) ∧
    -Real.log (1000 / 1349) ≤ (149681789 / 500000000) := by
  have h := checkLog_sound (w := (349 / 2349)) (n := 12)
    (lo := (299363577 / 1000000000)) (hi := (149681789 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1349 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1349 / 1000) = 1/(1000 / 1349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10435 : Bounds (299363577 / 1000000000) (149681789 / 500000000) (Real.log (1349 / 1000)) := by
  have h := reflection_log_10435_neg
  have he : Real.log (1349 / 1000) = -Real.log (1000 / 1349) := by
    rw [show ((1349 / 1000) : ℝ) = ((1000 / 1349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10436_neg : (107311409 / 250000000) ≤ -Real.log (651 / 1000) ∧
    -Real.log (651 / 1000) ≤ (429245637 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1651)) (n := 12)
    (lo := (107311409 / 250000000)) (hi := (429245637 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 651) = 1/(651 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10436 : Bounds (-429245637 / 1000000000) (-107311409 / 250000000) (Real.log (651 / 1000)) := by
  have h := reflection_log_10436_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10437_neg : (348939 / 1000000000) ≤ -Real.log (1000000 / 1000349) ∧
    -Real.log (1000000 / 1000349) ≤ (17447 / 50000000) := by
  have h := checkLog_sound (w := (349 / 2000349)) (n := 12)
    (lo := (348939 / 1000000000)) (hi := (17447 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000349 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000349 / 1000000) = 1/(1000000 / 1000349) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10437 : Bounds (348939 / 1000000000) (17447 / 50000000) (Real.log (1000349 / 1000000)) := by
  have h := reflection_log_10437_neg
  have he : Real.log (1000349 / 1000000) = -Real.log (1000000 / 1000349) := by
    rw [show ((1000349 / 1000000) : ℝ) = ((1000000 / 1000349) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10438_neg : (17453 / 50000000) ≤ -Real.log (999651 / 1000000) ∧
    -Real.log (999651 / 1000000) ≤ (349061 / 1000000000) := by
  have h := checkLog_sound (w := (349 / 1999651)) (n := 12)
    (lo := (17453 / 50000000)) (hi := (349061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999651) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999651) = 1/(999651 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10438 : Bounds (-349061 / 1000000000) (-17453 / 50000000) (Real.log (999651 / 1000000)) := by
  have h := reflection_log_10438_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10439_neg : (163623669 / 1000000000) ≤ -Real.log (1000000 / 1177771) ∧
    -Real.log (1000000 / 1177771) ≤ (16362367 / 100000000) := by
  have h := checkLog_sound (w := (177771 / 2177771)) (n := 12)
    (lo := (163623669 / 1000000000)) (hi := (16362367 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1177771 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1177771 / 1000000) = 1/(1000000 / 1177771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10439 : Bounds (163623669 / 1000000000) (16362367 / 100000000) (Real.log (1177771 / 1000000)) := by
  have h := reflection_log_10439_neg
  have he : Real.log (1177771 / 1000000) = -Real.log (1000000 / 1177771) := by
    rw [show ((1177771 / 1000000) : ℝ) = ((1000000 / 1177771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10440_neg : (195736333 / 1000000000) ≤ -Real.log (822229 / 1000000) ∧
    -Real.log (822229 / 1000000) ≤ (97868167 / 500000000) := by
  have h := checkLog_sound (w := (177771 / 1822229)) (n := 12)
    (lo := (195736333 / 1000000000)) (hi := (97868167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 822229) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 822229) = 1/(822229 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10440 : Bounds (-97868167 / 500000000) (-195736333 / 1000000000) (Real.log (822229 / 1000000)) := by
  have h := reflection_log_10440_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10441_neg : (82184009 / 500000000) ≤ -Real.log (125000 / 147331) ∧
    -Real.log (125000 / 147331) ≤ (164368019 / 1000000000) := by
  have h := checkLog_sound (w := (22331 / 272331)) (n := 12)
    (lo := (82184009 / 500000000)) (hi := (164368019 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147331 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147331 / 125000) = 1/(125000 / 147331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10441 : Bounds (82184009 / 500000000) (164368019 / 1000000000) (Real.log (147331 / 125000)) := by
  have h := reflection_log_10441_neg
  have he : Real.log (147331 / 125000) = -Real.log (125000 / 147331) := by
    rw [show ((147331 / 125000) : ℝ) = ((125000 / 147331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10442_neg : (39360703 / 200000000) ≤ -Real.log (102669 / 125000) ∧
    -Real.log (102669 / 125000) ≤ (49200879 / 250000000) := by
  have h := checkLog_sound (w := (22331 / 227669)) (n := 12)
    (lo := (39360703 / 200000000)) (hi := (49200879 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102669) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102669) = 1/(102669 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10442 : Bounds (-49200879 / 250000000) (-39360703 / 200000000) (Real.log (102669 / 125000)) := by
  have h := reflection_log_10442_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10443_neg : (32435497 / 1000000000) ≤ -Real.log (15126326439 / 15625000000) ∧
    -Real.log (15126326439 / 15625000000) ≤ (16217749 / 500000000) := by
  have h := checkLog_sound (w := (498673561 / 30751326439)) (n := 12)
    (lo := (32435497 / 1000000000)) (hi := (16217749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15126326439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15126326439) = 1/(15126326439 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10443 : Bounds (-16217749 / 500000000) (-32435497 / 1000000000) (Real.log (15126326439 / 15625000000)) := by
  have h := reflection_log_10443_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10444_neg : (4014083 / 125000000) ≤ -Real.log (968397471559 / 1000000000000) ∧
    -Real.log (968397471559 / 1000000000000) ≤ (6422533 / 200000000) := by
  have h := checkLog_sound (w := (31602528441 / 1968397471559)) (n := 12)
    (lo := (4014083 / 125000000)) (hi := (6422533 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968397471559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968397471559) = 1/(968397471559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10444 : Bounds (-6422533 / 200000000) (-4014083 / 125000000) (Real.log (968397471559 / 1000000000000)) := by
  have h := reflection_log_10444_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10445_neg : (179680001 / 500000000) ≤ -Real.log (125000000000 / 179051547683) ∧
    -Real.log (125000000000 / 179051547683) ≤ (359360003 / 1000000000) := by
  have h := checkLog_sound (w := (54051547683 / 304051547683)) (n := 12)
    (lo := (179680001 / 500000000)) (hi := (359360003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179051547683 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179051547683 / 125000000000) = 1/(125000000000 / 179051547683) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10445 : Bounds (179680001 / 500000000) (359360003 / 1000000000) (Real.log (179051547683 / 125000000000)) := by
  have h := reflection_log_10445_neg
  have he : Real.log (179051547683 / 125000000000) = -Real.log (125000000000 / 179051547683) := by
    rw [show ((179051547683 / 125000000000) : ℝ) = ((125000000000 / 179051547683) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10446_neg : (180585767 / 500000000) ≤ -Real.log (500000000000 / 717504796969) ∧
    -Real.log (500000000000 / 717504796969) ≤ (72234307 / 200000000) := by
  have h := checkLog_sound (w := (217504796969 / 1217504796969)) (n := 12)
    (lo := (180585767 / 500000000)) (hi := (72234307 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717504796969 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717504796969 / 500000000000) = 1/(500000000000 / 717504796969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10446 : Bounds (180585767 / 500000000) (72234307 / 200000000) (Real.log (717504796969 / 500000000000)) := by
  have h := reflection_log_10446_neg
  have he : Real.log (717504796969 / 500000000000) = -Real.log (500000000000 / 717504796969) := by
    rw [show ((717504796969 / 500000000000) : ℝ) = ((500000000000 / 717504796969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10447_neg : (90791591 / 125000000) ≤ -Real.log (62500000000 / 129217791411) ∧
    -Real.log (62500000000 / 129217791411) ≤ (72633273 / 100000000) := by
  have h := checkLog_sound (w := (4217791411 / 254217791411)) (n := 12)
    (lo := (8296387 / 250000000)) (hi := (33185549 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((129217791411 / 125000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(129217791411 / 125000000000) = 1/(62500000000 / 129217791411) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10447 : Bounds (90791591 / 125000000) (72633273 / 100000000) (Real.log (129217791411 / 62500000000)) := by
  have h := reflection_log_10447_neg
  have he : Real.log (129217791411 / 62500000000) = -Real.log (62500000000 / 129217791411) := by
    rw [show ((129217791411 / 62500000000) : ℝ) = ((62500000000 / 129217791411) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10448_neg : (728609213 / 1000000000) ≤ -Real.log (125000000000 / 259024577573) ∧
    -Real.log (125000000000 / 259024577573) ≤ (145721843 / 200000000) := by
  have h := checkLog_sound (w := (9024577573 / 509024577573)) (n := 12)
    (lo := (35462033 / 1000000000)) (hi := (17731017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((259024577573 / 250000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(259024577573 / 250000000000) = 1/(125000000000 / 259024577573) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10448 : Bounds (728609213 / 1000000000) (145721843 / 200000000) (Real.log (259024577573 / 125000000000)) := by
  have h := reflection_log_10448_neg
  have he : Real.log (259024577573 / 125000000000) = -Real.log (125000000000 / 259024577573) := by
    rw [show ((259024577573 / 125000000000) : ℝ) = ((125000000000 / 259024577573) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10449_neg : (18756537 / 62500000) ≤ -Real.log (20 / 27) ∧
    -Real.log (20 / 27) ≤ (300104593 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 47)) (n := 12)
    (lo := (18756537 / 62500000)) (hi := (300104593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((27 / 20) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(27 / 20) = 1/(20 / 27) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10449 : Bounds (18756537 / 62500000) (300104593 / 1000000000) (Real.log (27 / 20)) := by
  have h := reflection_log_10449_neg
  have he : Real.log (27 / 20) = -Real.log (20 / 27) := by
    rw [show ((27 / 20) : ℝ) = ((20 / 27) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10450_neg : (107695729 / 250000000) ≤ -Real.log (13 / 20) ∧
    -Real.log (13 / 20) ≤ (430782917 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 33)) (n := 12)
    (lo := (107695729 / 250000000)) (hi := (430782917 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20 / 13) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20 / 13) = 1/(13 / 20) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10450 : Bounds (-430782917 / 1000000000) (-107695729 / 250000000) (Real.log (13 / 20)) := by
  have h := reflection_log_10450_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10451_neg : (174969 / 500000000) ≤ -Real.log (20000 / 20007) ∧
    -Real.log (20000 / 20007) ≤ (349939 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 40007)) (n := 12)
    (lo := (174969 / 500000000)) (hi := (349939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20007 / 20000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20007 / 20000) = 1/(20000 / 20007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10451 : Bounds (174969 / 500000000) (349939 / 1000000000) (Real.log (20007 / 20000)) := by
  have h := reflection_log_10451_neg
  have he : Real.log (20007 / 20000) = -Real.log (20000 / 20007) := by
    rw [show ((20007 / 20000) : ℝ) = ((20000 / 20007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10452_neg : (350061 / 1000000000) ≤ -Real.log (19993 / 20000) ∧
    -Real.log (19993 / 20000) ≤ (175031 / 500000000) := by
  have h := checkLog_sound (w := (7 / 39993)) (n := 12)
    (lo := (350061 / 1000000000)) (hi := (175031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20000 / 19993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20000 / 19993) = 1/(19993 / 20000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10452 : Bounds (-175031 / 500000000) (-350061 / 1000000000) (Real.log (19993 / 20000)) := by
  have h := reflection_log_10452_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10453_neg : (164077813 / 1000000000) ≤ -Real.log (500000 / 589153) ∧
    -Real.log (500000 / 589153) ≤ (82038907 / 500000000) := by
  have h := checkLog_sound (w := (89153 / 1089153)) (n := 12)
    (lo := (164077813 / 1000000000)) (hi := (82038907 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((589153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(589153 / 500000) = 1/(500000 / 589153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10453 : Bounds (164077813 / 1000000000) (82038907 / 500000000) (Real.log (589153 / 500000)) := by
  have h := reflection_log_10453_neg
  have he : Real.log (589153 / 500000) = -Real.log (500000 / 589153) := by
    rw [show ((589153 / 500000) : ℝ) = ((500000 / 589153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10454_neg : (12274201 / 62500000) ≤ -Real.log (410847 / 500000) ∧
    -Real.log (410847 / 500000) ≤ (196387217 / 1000000000) := by
  have h := checkLog_sound (w := (89153 / 910847)) (n := 12)
    (lo := (12274201 / 62500000)) (hi := (196387217 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 410847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 410847) = 1/(410847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10454 : Bounds (-196387217 / 1000000000) (-12274201 / 62500000) (Real.log (410847 / 500000)) := by
  have h := reflection_log_10454_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10455_neg : (6592873 / 40000000) ≤ -Real.log (1000000 / 1179183) ∧
    -Real.log (1000000 / 1179183) ≤ (82410913 / 500000000) := by
  have h := checkLog_sound (w := (179183 / 2179183)) (n := 12)
    (lo := (6592873 / 40000000)) (hi := (82410913 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179183 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179183 / 1000000) = 1/(1000000 / 1179183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10455 : Bounds (6592873 / 40000000) (82410913 / 500000000) (Real.log (1179183 / 1000000)) := by
  have h := reflection_log_10455_neg
  have he : Real.log (1179183 / 1000000) = -Real.log (1000000 / 1179183) := by
    rw [show ((1179183 / 1000000) : ℝ) = ((1000000 / 1179183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10456_neg : (197455093 / 1000000000) ≤ -Real.log (820817 / 1000000) ∧
    -Real.log (820817 / 1000000) ≤ (98727547 / 500000000) := by
  have h := checkLog_sound (w := (179183 / 1820817)) (n := 12)
    (lo := (197455093 / 1000000000)) (hi := (98727547 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820817) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820817) = 1/(820817 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10456 : Bounds (-98727547 / 500000000) (-197455093 / 1000000000) (Real.log (820817 / 1000000)) := by
  have h := reflection_log_10456_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10457_neg : (32633267 / 1000000000) ≤ -Real.log (967893452511 / 1000000000000) ∧
    -Real.log (967893452511 / 1000000000000) ≤ (8158317 / 250000000) := by
  have h := checkLog_sound (w := (32106547489 / 1967893452511)) (n := 12)
    (lo := (32633267 / 1000000000)) (hi := (8158317 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967893452511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967893452511) = 1/(967893452511 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10457 : Bounds (-8158317 / 250000000) (-32633267 / 1000000000) (Real.log (967893452511 / 1000000000000)) := by
  have h := reflection_log_10457_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10458_neg : (16154701 / 500000000) ≤ -Real.log (242051742591 / 250000000000) ∧
    -Real.log (242051742591 / 250000000000) ≤ (32309403 / 1000000000) := by
  have h := checkLog_sound (w := (7948257409 / 492051742591)) (n := 12)
    (lo := (16154701 / 500000000)) (hi := (32309403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 242051742591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 242051742591) = 1/(242051742591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10458 : Bounds (-32309403 / 1000000000) (-16154701 / 500000000) (Real.log (242051742591 / 250000000000)) := by
  have h := reflection_log_10458_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10459_neg : (360465029 / 1000000000) ≤ -Real.log (500000000000 / 716998055237) ∧
    -Real.log (500000000000 / 716998055237) ≤ (36046503 / 100000000) := by
  have h := checkLog_sound (w := (216998055237 / 1216998055237)) (n := 12)
    (lo := (360465029 / 1000000000)) (hi := (36046503 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((716998055237 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(716998055237 / 500000000000) = 1/(500000000000 / 716998055237) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10459 : Bounds (360465029 / 1000000000) (36046503 / 100000000) (Real.log (716998055237 / 500000000000)) := by
  have h := reflection_log_10459_neg
  have he : Real.log (716998055237 / 500000000000) = -Real.log (500000000000 / 716998055237) := by
    rw [show ((716998055237 / 500000000000) : ℝ) = ((500000000000 / 716998055237) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10460_neg : (362276919 / 1000000000) ≤ -Real.log (250000000000 / 359149176979) ∧
    -Real.log (250000000000 / 359149176979) ≤ (9056923 / 25000000) := by
  have h := checkLog_sound (w := (109149176979 / 609149176979)) (n := 12)
    (lo := (362276919 / 1000000000)) (hi := (9056923 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359149176979 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359149176979 / 250000000000) = 1/(250000000000 / 359149176979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10460 : Bounds (362276919 / 1000000000) (9056923 / 25000000) (Real.log (359149176979 / 250000000000)) := by
  have h := reflection_log_10460_neg
  have he : Real.log (359149176979 / 250000000000) = -Real.log (250000000000 / 359149176979) := by
    rw [show ((359149176979 / 250000000000) : ℝ) = ((250000000000 / 359149176979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10461_neg : (728609213 / 1000000000) ≤ -Real.log (500000000000 / 1036098310291) ∧
    -Real.log (500000000000 / 1036098310291) ≤ (145721843 / 200000000) := by
  have h := checkLog_sound (w := (36098310291 / 2036098310291)) (n := 12)
    (lo := (35462033 / 1000000000)) (hi := (17731017 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1036098310291 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1036098310291 / 1000000000000) = 1/(500000000000 / 1036098310291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10461 : Bounds (728609213 / 1000000000) (145721843 / 200000000) (Real.log (1036098310291 / 500000000000)) := by
  have h := reflection_log_10461_neg
  have he : Real.log (1036098310291 / 500000000000) = -Real.log (500000000000 / 1036098310291) := by
    rw [show ((1036098310291 / 500000000000) : ℝ) = ((500000000000 / 1036098310291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10462_neg : (730887507 / 1000000000) ≤ -Real.log (250000000000 / 519230769231) ∧
    -Real.log (250000000000 / 519230769231) ≤ (730887509 / 1000000000) := by
  have h := checkLog_sound (w := (19230769231 / 1019230769231)) (n := 12)
    (lo := (37740327 / 1000000000)) (hi := (4717541 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((519230769231 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(519230769231 / 500000000000) = 1/(250000000000 / 519230769231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10462 : Bounds (730887507 / 1000000000) (730887509 / 1000000000) (Real.log (519230769231 / 250000000000)) := by
  have h := reflection_log_10462_neg
  have he : Real.log (519230769231 / 250000000000) = -Real.log (250000000000 / 519230769231) := by
    rw [show ((519230769231 / 250000000000) : ℝ) = ((250000000000 / 519230769231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10463_neg : (150422529 / 500000000) ≤ -Real.log (1000 / 1351) ∧
    -Real.log (1000 / 1351) ≤ (300845059 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 2351)) (n := 12)
    (lo := (150422529 / 500000000)) (hi := (300845059 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1351 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1351 / 1000) = 1/(1000 / 1351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10463 : Bounds (150422529 / 500000000) (300845059 / 1000000000) (Real.log (1351 / 1000)) := by
  have h := reflection_log_10463_neg
  have he : Real.log (1351 / 1000) = -Real.log (1000 / 1351) := by
    rw [show ((1351 / 1000) : ℝ) = ((1000 / 1351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10464_neg : (216161281 / 500000000) ≤ -Real.log (649 / 1000) ∧
    -Real.log (649 / 1000) ≤ (432322563 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 1649)) (n := 12)
    (lo := (216161281 / 500000000)) (hi := (432322563 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 649) = 1/(649 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10464 : Bounds (-432322563 / 1000000000) (-216161281 / 500000000) (Real.log (649 / 1000)) := by
  have h := reflection_log_10464_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10465_neg : (175469 / 500000000) ≤ -Real.log (1000000 / 1000351) ∧
    -Real.log (1000000 / 1000351) ≤ (350939 / 1000000000) := by
  have h := checkLog_sound (w := (351 / 2000351)) (n := 12)
    (lo := (175469 / 500000000)) (hi := (350939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000351 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000351 / 1000000) = 1/(1000000 / 1000351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10465 : Bounds (175469 / 500000000) (350939 / 1000000000) (Real.log (1000351 / 1000000)) := by
  have h := reflection_log_10465_neg
  have he : Real.log (1000351 / 1000000) = -Real.log (1000000 / 1000351) := by
    rw [show ((1000351 / 1000000) : ℝ) = ((1000000 / 1000351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10466_neg : (351061 / 1000000000) ≤ -Real.log (999649 / 1000000) ∧
    -Real.log (999649 / 1000000) ≤ (175531 / 500000000) := by
  have h := checkLog_sound (w := (351 / 1999649)) (n := 12)
    (lo := (351061 / 1000000000)) (hi := (175531 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999649) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999649) = 1/(999649 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10466 : Bounds (-175531 / 500000000) (-351061 / 1000000000) (Real.log (999649 / 1000000)) := by
  have h := reflection_log_10466_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10467_neg : (20566469 / 125000000) ≤ -Real.log (1000000 / 1178841) ∧
    -Real.log (1000000 / 1178841) ≤ (164531753 / 1000000000) := by
  have h := checkLog_sound (w := (178841 / 2178841)) (n := 12)
    (lo := (20566469 / 125000000)) (hi := (164531753 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1178841 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1178841 / 1000000) = 1/(1000000 / 1178841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10467 : Bounds (20566469 / 125000000) (164531753 / 1000000000) (Real.log (1178841 / 1000000)) := by
  have h := reflection_log_10467_neg
  have he : Real.log (1178841 / 1000000) = -Real.log (1000000 / 1178841) := by
    rw [show ((1178841 / 1000000) : ℝ) = ((1000000 / 1178841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10468_neg : (98519261 / 500000000) ≤ -Real.log (821159 / 1000000) ∧
    -Real.log (821159 / 1000000) ≤ (197038523 / 1000000000) := by
  have h := checkLog_sound (w := (178841 / 1821159)) (n := 12)
    (lo := (98519261 / 500000000)) (hi := (197038523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 821159) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 821159) = 1/(821159 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10468 : Bounds (-197038523 / 1000000000) (-98519261 / 500000000) (Real.log (821159 / 1000000)) := by
  have h := reflection_log_10468_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10469_neg : (82638137 / 500000000) ≤ -Real.log (1000000 / 1179719) ∧
    -Real.log (1000000 / 1179719) ≤ (6611051 / 40000000) := by
  have h := checkLog_sound (w := (179719 / 2179719)) (n := 12)
    (lo := (82638137 / 500000000)) (hi := (6611051 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179719 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179719 / 1000000) = 1/(1000000 / 1179719) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10469 : Bounds (82638137 / 500000000) (6611051 / 40000000) (Real.log (1179719 / 1000000)) := by
  have h := reflection_log_10469_neg
  have he : Real.log (1179719 / 1000000) = -Real.log (1000000 / 1179719) := by
    rw [show ((1179719 / 1000000) : ℝ) = ((1000000 / 1179719) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10470_neg : (99054157 / 500000000) ≤ -Real.log (820281 / 1000000) ∧
    -Real.log (820281 / 1000000) ≤ (39621663 / 200000000) := by
  have h := checkLog_sound (w := (179719 / 1820281)) (n := 12)
    (lo := (99054157 / 500000000)) (hi := (39621663 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820281) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820281) = 1/(820281 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10470 : Bounds (-39621663 / 200000000) (-99054157 / 500000000) (Real.log (820281 / 1000000)) := by
  have h := reflection_log_10470_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10471_neg : (32832039 / 1000000000) ≤ -Real.log (967701081039 / 1000000000000) ∧
    -Real.log (967701081039 / 1000000000000) ≤ (820801 / 25000000) := by
  have h := checkLog_sound (w := (32298918961 / 1967701081039)) (n := 12)
    (lo := (32832039 / 1000000000)) (hi := (820801 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967701081039) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967701081039) = 1/(967701081039 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10471 : Bounds (-820801 / 25000000) (-32832039 / 1000000000) (Real.log (967701081039 / 1000000000000)) := by
  have h := reflection_log_10471_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10472_neg : (32506769 / 1000000000) ≤ -Real.log (968015896719 / 1000000000000) ∧
    -Real.log (968015896719 / 1000000000000) ≤ (3250677 / 100000000) := by
  have h := checkLog_sound (w := (31984103281 / 1968015896719)) (n := 12)
    (lo := (32506769 / 1000000000)) (hi := (3250677 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 968015896719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 968015896719) = 1/(968015896719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10472 : Bounds (-3250677 / 100000000) (-32506769 / 1000000000) (Real.log (968015896719 / 1000000000000)) := by
  have h := reflection_log_10472_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10473_neg : (180785137 / 500000000) ≤ -Real.log (500000000000 / 717790951569) ∧
    -Real.log (500000000000 / 717790951569) ≤ (14462811 / 40000000) := by
  have h := checkLog_sound (w := (217790951569 / 1217790951569)) (n := 12)
    (lo := (180785137 / 500000000)) (hi := (14462811 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((717790951569 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(717790951569 / 500000000000) = 1/(500000000000 / 717790951569) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10473 : Bounds (180785137 / 500000000) (14462811 / 40000000) (Real.log (717790951569 / 500000000000)) := by
  have h := reflection_log_10473_neg
  have he : Real.log (717790951569 / 500000000000) = -Real.log (500000000000 / 717790951569) := by
    rw [show ((717790951569 / 500000000000) : ℝ) = ((500000000000 / 717790951569) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10474_neg : (363384589 / 1000000000) ≤ -Real.log (250000000000 / 359547216137) ∧
    -Real.log (250000000000 / 359547216137) ≤ (36338459 / 100000000) := by
  have h := checkLog_sound (w := (109547216137 / 609547216137)) (n := 12)
    (lo := (363384589 / 1000000000)) (hi := (36338459 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359547216137 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359547216137 / 250000000000) = 1/(250000000000 / 359547216137) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10474 : Bounds (363384589 / 1000000000) (36338459 / 100000000) (Real.log (359547216137 / 250000000000)) := by
  have h := reflection_log_10474_neg
  have he : Real.log (359547216137 / 250000000000) = -Real.log (250000000000 / 359547216137) := by
    rw [show ((359547216137 / 250000000000) : ℝ) = ((250000000000 / 359547216137) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10475_neg : (730887507 / 1000000000) ≤ -Real.log (500000000000 / 1038461538461) ∧
    -Real.log (500000000000 / 1038461538461) ≤ (730887509 / 1000000000) := by
  have h := checkLog_sound (w := (38461538461 / 2038461538461)) (n := 12)
    (lo := (37740327 / 1000000000)) (hi := (4717541 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1038461538461 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1038461538461 / 1000000000000) = 1/(500000000000 / 1038461538461) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10475 : Bounds (730887507 / 1000000000) (730887509 / 1000000000) (Real.log (1038461538461 / 500000000000)) := by
  have h := reflection_log_10475_neg
  have he : Real.log (1038461538461 / 500000000000) = -Real.log (500000000000 / 1038461538461) := by
    rw [show ((1038461538461 / 500000000000) : ℝ) = ((500000000000 / 1038461538461) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10476_neg : (36658381 / 50000000) ≤ -Real.log (500000000000 / 1040832049307) ∧
    -Real.log (500000000000 / 1040832049307) ≤ (366583811 / 500000000) := by
  have h := checkLog_sound (w := (40832049307 / 2040832049307)) (n := 12)
    (lo := (1000511 / 25000000)) (hi := (40020441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1040832049307 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1040832049307 / 1000000000000) = 1/(500000000000 / 1040832049307) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10476 : Bounds (36658381 / 50000000) (366583811 / 500000000) (Real.log (1040832049307 / 500000000000)) := by
  have h := reflection_log_10476_neg
  have he : Real.log (1040832049307 / 500000000000) = -Real.log (500000000000 / 1040832049307) := by
    rw [show ((1040832049307 / 500000000000) : ℝ) = ((500000000000 / 1040832049307) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10477_neg : (301584977 / 1000000000) ≤ -Real.log (125 / 169) ∧
    -Real.log (125 / 169) ≤ (150792489 / 500000000) := by
  have h := checkLog_sound (w := (22 / 147)) (n := 12)
    (lo := (301584977 / 1000000000)) (hi := (150792489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((169 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(169 / 125) = 1/(125 / 169) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10477 : Bounds (301584977 / 1000000000) (150792489 / 500000000) (Real.log (169 / 125)) := by
  have h := reflection_log_10477_neg
  have he : Real.log (169 / 125) = -Real.log (125 / 169) := by
    rw [show ((169 / 125) : ℝ) = ((125 / 169) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10478_neg : (216932291 / 500000000) ≤ -Real.log (81 / 125) ∧
    -Real.log (81 / 125) ≤ (433864583 / 1000000000) := by
  have h := checkLog_sound (w := (22 / 103)) (n := 12)
    (lo := (216932291 / 500000000)) (hi := (433864583 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 81) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 81) = 1/(81 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10478 : Bounds (-433864583 / 1000000000) (-216932291 / 500000000) (Real.log (81 / 125)) := by
  have h := reflection_log_10478_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10479_neg : (175969 / 500000000) ≤ -Real.log (31250 / 31261) ∧
    -Real.log (31250 / 31261) ≤ (351939 / 1000000000) := by
  have h := checkLog_sound (w := (11 / 62511)) (n := 12)
    (lo := (175969 / 500000000)) (hi := (351939 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31261 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31261 / 31250) = 1/(31250 / 31261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10479 : Bounds (175969 / 500000000) (351939 / 1000000000) (Real.log (31261 / 31250)) := by
  have h := reflection_log_10479_neg
  have he : Real.log (31261 / 31250) = -Real.log (31250 / 31261) := by
    rw [show ((31261 / 31250) : ℝ) = ((31250 / 31261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10480_neg : (352061 / 1000000000) ≤ -Real.log (31239 / 31250) ∧
    -Real.log (31239 / 31250) ≤ (176031 / 500000000) := by
  have h := checkLog_sound (w := (11 / 62489)) (n := 12)
    (lo := (352061 / 1000000000)) (hi := (176031 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 31239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 31239) = 1/(31239 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10480 : Bounds (-176031 / 500000000) (-352061 / 1000000000) (Real.log (31239 / 31250)) := by
  have h := reflection_log_10480_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10481_neg : (32997097 / 200000000) ≤ -Real.log (62500 / 73711) ∧
    -Real.log (62500 / 73711) ≤ (82492743 / 500000000) := by
  have h := checkLog_sound (w := (11211 / 136211)) (n := 12)
    (lo := (32997097 / 200000000)) (hi := (82492743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73711 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73711 / 62500) = 1/(62500 / 73711) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10481 : Bounds (32997097 / 200000000) (82492743 / 500000000) (Real.log (73711 / 62500)) := by
  have h := reflection_log_10481_neg
  have he : Real.log (73711 / 62500) = -Real.log (62500 / 73711) := by
    rw [show ((73711 / 62500) : ℝ) = ((62500 / 73711) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10482_neg : (49422563 / 250000000) ≤ -Real.log (51289 / 62500) ∧
    -Real.log (51289 / 62500) ≤ (197690253 / 1000000000) := by
  have h := checkLog_sound (w := (11211 / 113789)) (n := 12)
    (lo := (49422563 / 250000000)) (hi := (197690253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51289) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51289) = 1/(51289 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10482 : Bounds (-197690253 / 1000000000) (-49422563 / 250000000) (Real.log (51289 / 62500)) := by
  have h := reflection_log_10482_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10483_neg : (41432629 / 250000000) ≤ -Real.log (200000 / 236051) ∧
    -Real.log (200000 / 236051) ≤ (165730517 / 1000000000) := by
  have h := checkLog_sound (w := (36051 / 436051)) (n := 12)
    (lo := (41432629 / 250000000)) (hi := (165730517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236051 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236051 / 200000) = 1/(200000 / 236051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10483 : Bounds (41432629 / 250000000) (165730517 / 1000000000) (Real.log (236051 / 200000)) := by
  have h := reflection_log_10483_neg
  have he : Real.log (236051 / 200000) = -Real.log (200000 / 236051) := by
    rw [show ((236051 / 200000) : ℝ) = ((200000 / 236051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10484_neg : (99380981 / 500000000) ≤ -Real.log (163949 / 200000) ∧
    -Real.log (163949 / 200000) ≤ (198761963 / 1000000000) := by
  have h := checkLog_sound (w := (36051 / 363949)) (n := 12)
    (lo := (99380981 / 500000000)) (hi := (198761963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163949) = 1/(163949 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10484 : Bounds (-198761963 / 1000000000) (-99380981 / 500000000) (Real.log (163949 / 200000)) := by
  have h := reflection_log_10484_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10485_neg : (6606289 / 200000000) ≤ -Real.log (38700325399 / 40000000000) ∧
    -Real.log (38700325399 / 40000000000) ≤ (16515723 / 500000000) := by
  have h := checkLog_sound (w := (1299674601 / 78700325399)) (n := 12)
    (lo := (6606289 / 200000000)) (hi := (16515723 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38700325399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38700325399) = 1/(38700325399 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10485 : Bounds (-16515723 / 500000000) (-6606289 / 200000000) (Real.log (38700325399 / 40000000000)) := by
  have h := reflection_log_10485_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10486_neg : (32704767 / 1000000000) ≤ -Real.log (3780563479 / 3906250000) ∧
    -Real.log (3780563479 / 3906250000) ≤ (127753 / 3906250) := by
  have h := checkLog_sound (w := (125686521 / 7686813479)) (n := 12)
    (lo := (32704767 / 1000000000)) (hi := (127753 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3780563479) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3780563479) = 1/(3780563479 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10486 : Bounds (-127753 / 3906250) (-32704767 / 1000000000) (Real.log (3780563479 / 3906250000)) := by
  have h := reflection_log_10486_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10487_neg : (362675737 / 1000000000) ≤ -Real.log (125000000000 / 179646220437) ∧
    -Real.log (125000000000 / 179646220437) ≤ (181337869 / 500000000) := by
  have h := checkLog_sound (w := (54646220437 / 304646220437)) (n := 12)
    (lo := (362675737 / 1000000000)) (hi := (181337869 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((179646220437 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(179646220437 / 125000000000) = 1/(125000000000 / 179646220437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10487 : Bounds (362675737 / 1000000000) (181337869 / 500000000) (Real.log (179646220437 / 125000000000)) := by
  have h := reflection_log_10487_neg
  have he : Real.log (179646220437 / 125000000000) = -Real.log (125000000000 / 179646220437) := by
    rw [show ((179646220437 / 125000000000) : ℝ) = ((125000000000 / 179646220437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10488_neg : (364492479 / 1000000000) ≤ -Real.log (250000000000 / 359945775821) ∧
    -Real.log (250000000000 / 359945775821) ≤ (1139039 / 3125000) := by
  have h := checkLog_sound (w := (109945775821 / 609945775821)) (n := 12)
    (lo := (364492479 / 1000000000)) (hi := (1139039 / 3125000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((359945775821 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(359945775821 / 250000000000) = 1/(250000000000 / 359945775821) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10488 : Bounds (364492479 / 1000000000) (1139039 / 3125000) (Real.log (359945775821 / 250000000000)) := by
  have h := reflection_log_10488_neg
  have he : Real.log (359945775821 / 250000000000) = -Real.log (250000000000 / 359945775821) := by
    rw [show ((359945775821 / 250000000000) : ℝ) = ((250000000000 / 359945775821) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10489_neg : (36658381 / 50000000) ≤ -Real.log (250000000000 / 520416024653) ∧
    -Real.log (250000000000 / 520416024653) ≤ (366583811 / 500000000) := by
  have h := checkLog_sound (w := (20416024653 / 1020416024653)) (n := 12)
    (lo := (1000511 / 25000000)) (hi := (40020441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((520416024653 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(520416024653 / 500000000000) = 1/(250000000000 / 520416024653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10489 : Bounds (36658381 / 50000000) (366583811 / 500000000) (Real.log (520416024653 / 250000000000)) := by
  have h := reflection_log_10489_neg
  have he : Real.log (520416024653 / 250000000000) = -Real.log (250000000000 / 520416024653) := by
    rw [show ((520416024653 / 250000000000) : ℝ) = ((250000000000 / 520416024653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10490_neg : (735449559 / 1000000000) ≤ -Real.log (7812500000 / 16300154321) ∧
    -Real.log (7812500000 / 16300154321) ≤ (735449561 / 1000000000) := by
  have h := checkLog_sound (w := (675154321 / 31925154321)) (n := 12)
    (lo := (42302379 / 1000000000)) (hi := (2115119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16300154321 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16300154321 / 15625000000) = 1/(7812500000 / 16300154321) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10490 : Bounds (735449559 / 1000000000) (735449561 / 1000000000) (Real.log (16300154321 / 7812500000)) := by
  have h := reflection_log_10490_neg
  have he : Real.log (16300154321 / 7812500000) = -Real.log (7812500000 / 16300154321) := by
    rw [show ((16300154321 / 7812500000) : ℝ) = ((7812500000 / 16300154321) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10491_neg : (302324349 / 1000000000) ≤ -Real.log (1000 / 1353) ∧
    -Real.log (1000 / 1353) ≤ (6046487 / 20000000) := by
  have h := checkLog_sound (w := (353 / 2353)) (n := 12)
    (lo := (302324349 / 1000000000)) (hi := (6046487 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1353 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1353 / 1000) = 1/(1000 / 1353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10491 : Bounds (302324349 / 1000000000) (6046487 / 20000000) (Real.log (1353 / 1000)) := by
  have h := reflection_log_10491_neg
  have he : Real.log (1353 / 1000) = -Real.log (1000 / 1353) := by
    rw [show ((1353 / 1000) : ℝ) = ((1000 / 1353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10492_neg : (54426123 / 125000000) ≤ -Real.log (647 / 1000) ∧
    -Real.log (647 / 1000) ≤ (87081797 / 200000000) := by
  have h := checkLog_sound (w := (353 / 1647)) (n := 12)
    (lo := (54426123 / 125000000)) (hi := (87081797 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 647) = 1/(647 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10492 : Bounds (-87081797 / 200000000) (-54426123 / 125000000) (Real.log (647 / 1000)) := by
  have h := reflection_log_10492_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10493_neg : (352937 / 1000000000) ≤ -Real.log (1000000 / 1000353) ∧
    -Real.log (1000000 / 1000353) ≤ (176469 / 500000000) := by
  have h := checkLog_sound (w := (353 / 2000353)) (n := 12)
    (lo := (352937 / 1000000000)) (hi := (176469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000353 / 1000000) = 1/(1000000 / 1000353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10493 : Bounds (352937 / 1000000000) (176469 / 500000000) (Real.log (1000353 / 1000000)) := by
  have h := reflection_log_10493_neg
  have he : Real.log (1000353 / 1000000) = -Real.log (1000000 / 1000353) := by
    rw [show ((1000353 / 1000000) : ℝ) = ((1000000 / 1000353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10494_neg : (176531 / 500000000) ≤ -Real.log (999647 / 1000000) ∧
    -Real.log (999647 / 1000000) ≤ (353063 / 1000000000) := by
  have h := checkLog_sound (w := (353 / 1999647)) (n := 12)
    (lo := (176531 / 500000000)) (hi := (353063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999647) = 1/(999647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10494 : Bounds (-353063 / 1000000000) (-176531 / 500000000) (Real.log (999647 / 1000000)) := by
  have h := reflection_log_10494_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10495_neg : (165439011 / 1000000000) ≤ -Real.log (1000000 / 1179911) ∧
    -Real.log (1000000 / 1179911) ≤ (41359753 / 250000000) := by
  have h := checkLog_sound (w := (179911 / 2179911)) (n := 12)
    (lo := (165439011 / 1000000000)) (hi := (41359753 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1179911 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1179911 / 1000000) = 1/(1000000 / 1179911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10495 : Bounds (165439011 / 1000000000) (41359753 / 250000000) (Real.log (1179911 / 1000000)) := by
  have h := reflection_log_10495_neg
  have he : Real.log (1179911 / 1000000) = -Real.log (1000000 / 1179911) := by
    rw [show ((1179911 / 1000000) : ℝ) = ((1000000 / 1179911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0164 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10496_neg : (24792801 / 125000000) ≤ -Real.log (820089 / 1000000) ∧
    -Real.log (820089 / 1000000) ≤ (198342409 / 1000000000) := by
  have h := checkLog_sound (w := (179911 / 1820089)) (n := 12)
    (lo := (24792801 / 125000000)) (hi := (198342409 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 820089) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 820089) = 1/(820089 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10496 : Bounds (-198342409 / 1000000000) (-24792801 / 125000000) (Real.log (820089 / 1000000)) := by
  have h := reflection_log_10496_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10497_neg : (166185399 / 1000000000) ≤ -Real.log (125000 / 147599) ∧
    -Real.log (125000 / 147599) ≤ (830927 / 5000000) := by
  have h := checkLog_sound (w := (22599 / 272599)) (n := 12)
    (lo := (166185399 / 1000000000)) (hi := (830927 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147599 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147599 / 125000) = 1/(125000 / 147599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10497 : Bounds (166185399 / 1000000000) (830927 / 5000000) (Real.log (147599 / 125000)) := by
  have h := reflection_log_10497_neg
  have he : Real.log (147599 / 125000) = -Real.log (125000 / 147599) := by
    rw [show ((147599 / 125000) : ℝ) = ((125000 / 147599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10498_neg : (199417259 / 1000000000) ≤ -Real.log (102401 / 125000) ∧
    -Real.log (102401 / 125000) ≤ (9970863 / 50000000) := by
  have h := checkLog_sound (w := (22599 / 227401)) (n := 12)
    (lo := (199417259 / 1000000000)) (hi := (9970863 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 102401) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 102401) = 1/(102401 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10498 : Bounds (-9970863 / 50000000) (-199417259 / 1000000000) (Real.log (102401 / 125000)) := by
  have h := reflection_log_10498_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10499_neg : (33231859 / 1000000000) ≤ -Real.log (15114285199 / 15625000000) ∧
    -Real.log (15114285199 / 15625000000) ≤ (1661593 / 50000000) := by
  have h := checkLog_sound (w := (510714801 / 30739285199)) (n := 12)
    (lo := (33231859 / 1000000000)) (hi := (1661593 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15114285199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15114285199) = 1/(15114285199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10499 : Bounds (-1661593 / 50000000) (-33231859 / 1000000000) (Real.log (15114285199 / 15625000000)) := by
  have h := reflection_log_10499_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10500_neg : (8225849 / 250000000) ≤ -Real.log (967632032079 / 1000000000000) ∧
    -Real.log (967632032079 / 1000000000000) ≤ (32903397 / 1000000000) := by
  have h := checkLog_sound (w := (32367967921 / 1967632032079)) (n := 12)
    (lo := (8225849 / 250000000)) (hi := (32903397 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967632032079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967632032079) = 1/(967632032079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10500 : Bounds (-32903397 / 1000000000) (-8225849 / 250000000) (Real.log (967632032079 / 1000000000000)) := by
  have h := reflection_log_10500_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10501_neg : (363781419 / 1000000000) ≤ -Real.log (500000000000 / 719379847797) ∧
    -Real.log (500000000000 / 719379847797) ≤ (18189071 / 50000000) := by
  have h := checkLog_sound (w := (219379847797 / 1219379847797)) (n := 12)
    (lo := (363781419 / 1000000000)) (hi := (18189071 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((719379847797 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(719379847797 / 500000000000) = 1/(500000000000 / 719379847797) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10501 : Bounds (363781419 / 1000000000) (18189071 / 50000000) (Real.log (719379847797 / 500000000000)) := by
  have h := reflection_log_10501_neg
  have he : Real.log (719379847797 / 500000000000) = -Real.log (500000000000 / 719379847797) := by
    rw [show ((719379847797 / 500000000000) : ℝ) = ((500000000000 / 719379847797) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10502_neg : (182801329 / 500000000) ≤ -Real.log (125000000000 / 180172801047) ∧
    -Real.log (125000000000 / 180172801047) ≤ (365602659 / 1000000000) := by
  have h := checkLog_sound (w := (55172801047 / 305172801047)) (n := 12)
    (lo := (182801329 / 500000000)) (hi := (365602659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180172801047 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180172801047 / 125000000000) = 1/(125000000000 / 180172801047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10502 : Bounds (182801329 / 500000000) (365602659 / 1000000000) (Real.log (180172801047 / 125000000000)) := by
  have h := reflection_log_10502_neg
  have he : Real.log (180172801047 / 125000000000) = -Real.log (125000000000 / 180172801047) := by
    rw [show ((180172801047 / 125000000000) : ℝ) = ((125000000000 / 180172801047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10503_neg : (735449559 / 1000000000) ≤ -Real.log (500000000000 / 1043209876543) ∧
    -Real.log (500000000000 / 1043209876543) ≤ (735449561 / 1000000000) := by
  have h := checkLog_sound (w := (43209876543 / 2043209876543)) (n := 12)
    (lo := (42302379 / 1000000000)) (hi := (2115119 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1043209876543 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1043209876543 / 1000000000000) = 1/(500000000000 / 1043209876543) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10503 : Bounds (735449559 / 1000000000) (735449561 / 1000000000) (Real.log (1043209876543 / 500000000000)) := by
  have h := reflection_log_10503_neg
  have he : Real.log (1043209876543 / 500000000000) = -Real.log (500000000000 / 1043209876543) := by
    rw [show ((1043209876543 / 500000000000) : ℝ) = ((500000000000 / 1043209876543) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10504_neg : (737733333 / 1000000000) ≤ -Real.log (31250000000 / 65349690881) ∧
    -Real.log (31250000000 / 65349690881) ≤ (147546667 / 200000000) := by
  have h := checkLog_sound (w := (2849690881 / 127849690881)) (n := 12)
    (lo := (44586153 / 1000000000)) (hi := (22293077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65349690881 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65349690881 / 62500000000) = 1/(31250000000 / 65349690881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10504 : Bounds (737733333 / 1000000000) (147546667 / 200000000) (Real.log (65349690881 / 31250000000)) := by
  have h := reflection_log_10504_neg
  have he : Real.log (65349690881 / 31250000000) = -Real.log (31250000000 / 65349690881) := by
    rw [show ((65349690881 / 31250000000) : ℝ) = ((31250000000 / 65349690881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10505_neg : (151531587 / 500000000) ≤ -Real.log (500 / 677) ∧
    -Real.log (500 / 677) ≤ (12122527 / 40000000) := by
  have h := checkLog_sound (w := (177 / 1177)) (n := 12)
    (lo := (151531587 / 500000000)) (hi := (12122527 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((677 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(677 / 500) = 1/(500 / 677) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10505 : Bounds (151531587 / 500000000) (12122527 / 40000000) (Real.log (677 / 500)) := by
  have h := reflection_log_10505_neg
  have he : Real.log (677 / 500) = -Real.log (500 / 677) := by
    rw [show ((677 / 500) : ℝ) = ((500 / 677) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10506_neg : (17478231 / 40000000) ≤ -Real.log (323 / 500) ∧
    -Real.log (323 / 500) ≤ (3413717 / 7812500) := by
  have h := checkLog_sound (w := (177 / 823)) (n := 12)
    (lo := (17478231 / 40000000)) (hi := (3413717 / 7812500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 323) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 323) = 1/(323 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10506 : Bounds (-3413717 / 7812500) (-17478231 / 40000000) (Real.log (323 / 500)) := by
  have h := reflection_log_10506_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10507_neg : (353937 / 1000000000) ≤ -Real.log (500000 / 500177) ∧
    -Real.log (500000 / 500177) ≤ (176969 / 500000000) := by
  have h := checkLog_sound (w := (177 / 1000177)) (n := 12)
    (lo := (353937 / 1000000000)) (hi := (176969 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500177 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500177 / 500000) = 1/(500000 / 500177) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10507 : Bounds (353937 / 1000000000) (176969 / 500000000) (Real.log (500177 / 500000)) := by
  have h := reflection_log_10507_neg
  have he : Real.log (500177 / 500000) = -Real.log (500000 / 500177) := by
    rw [show ((500177 / 500000) : ℝ) = ((500000 / 500177) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10508_neg : (177031 / 500000000) ≤ -Real.log (499823 / 500000) ∧
    -Real.log (499823 / 500000) ≤ (354063 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 999823)) (n := 12)
    (lo := (177031 / 500000000)) (hi := (354063 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499823) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499823) = 1/(499823 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10508 : Bounds (-354063 / 1000000000) (-177031 / 500000000) (Real.log (499823 / 500000)) := by
  have h := reflection_log_10508_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10509_neg : (165892333 / 1000000000) ≤ -Real.log (500000 / 590223) ∧
    -Real.log (500000 / 590223) ≤ (82946167 / 500000000) := by
  have h := checkLog_sound (w := (90223 / 1090223)) (n := 12)
    (lo := (165892333 / 1000000000)) (hi := (82946167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590223 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590223 / 500000) = 1/(500000 / 590223) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10509 : Bounds (165892333 / 1000000000) (82946167 / 500000000) (Real.log (590223 / 500000)) := by
  have h := reflection_log_10509_neg
  have he : Real.log (590223 / 500000) = -Real.log (500000 / 590223) := by
    rw [show ((590223 / 500000) : ℝ) = ((500000 / 590223) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10510_neg : (198994989 / 1000000000) ≤ -Real.log (409777 / 500000) ∧
    -Real.log (409777 / 500000) ≤ (19899499 / 100000000) := by
  have h := checkLog_sound (w := (90223 / 909777)) (n := 12)
    (lo := (198994989 / 1000000000)) (hi := (19899499 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409777) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409777) = 1/(409777 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10510 : Bounds (-19899499 / 100000000) (-198994989 / 1000000000) (Real.log (409777 / 500000)) := by
  have h := reflection_log_10510_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10511_neg : (166639229 / 1000000000) ≤ -Real.log (62500 / 73833) ∧
    -Real.log (62500 / 73833) ≤ (16663923 / 100000000) := by
  have h := checkLog_sound (w := (11333 / 136333)) (n := 12)
    (lo := (166639229 / 1000000000)) (hi := (16663923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((73833 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(73833 / 62500) = 1/(62500 / 73833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10511 : Bounds (166639229 / 1000000000) (16663923 / 100000000) (Real.log (73833 / 62500)) := by
  have h := reflection_log_10511_neg
  have he : Real.log (73833 / 62500) = -Real.log (62500 / 73833) := by
    rw [show ((73833 / 62500) : ℝ) = ((62500 / 73833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10512_neg : (200071763 / 1000000000) ≤ -Real.log (51167 / 62500) ∧
    -Real.log (51167 / 62500) ≤ (50017941 / 250000000) := by
  have h := checkLog_sound (w := (11333 / 113667)) (n := 12)
    (lo := (200071763 / 1000000000)) (hi := (50017941 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 51167) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 51167) = 1/(51167 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10512 : Bounds (-50017941 / 250000000) (-200071763 / 1000000000) (Real.log (51167 / 62500)) := by
  have h := reflection_log_10512_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10513_neg : (16716267 / 500000000) ≤ -Real.log (3777813111 / 3906250000) ∧
    -Real.log (3777813111 / 3906250000) ≤ (6686507 / 200000000) := by
  have h := checkLog_sound (w := (128436889 / 7684063111)) (n := 12)
    (lo := (16716267 / 500000000)) (hi := (6686507 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3906250000 / 3777813111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3906250000 / 3777813111) = 1/(3777813111 / 3906250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10513 : Bounds (-6686507 / 200000000) (-16716267 / 500000000) (Real.log (3777813111 / 3906250000)) := by
  have h := reflection_log_10513_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10514_neg : (6620531 / 200000000) ≤ -Real.log (241859810271 / 250000000000) ∧
    -Real.log (241859810271 / 250000000000) ≤ (517229 / 15625000) := by
  have h := checkLog_sound (w := (8140189729 / 491859810271)) (n := 12)
    (lo := (6620531 / 200000000)) (hi := (517229 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241859810271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241859810271) = 1/(241859810271 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10514 : Bounds (-517229 / 15625000) (-6620531 / 200000000) (Real.log (241859810271 / 250000000000)) := by
  have h := reflection_log_10514_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10515_neg : (182443661 / 500000000) ≤ -Real.log (500000000000 / 720175851743) ∧
    -Real.log (500000000000 / 720175851743) ≤ (364887323 / 1000000000) := by
  have h := checkLog_sound (w := (220175851743 / 1220175851743)) (n := 12)
    (lo := (182443661 / 500000000)) (hi := (364887323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720175851743 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720175851743 / 500000000000) = 1/(500000000000 / 720175851743) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10515 : Bounds (182443661 / 500000000) (364887323 / 1000000000) (Real.log (720175851743 / 500000000000)) := by
  have h := reflection_log_10515_neg
  have he : Real.log (720175851743 / 500000000000) = -Real.log (500000000000 / 720175851743) := by
    rw [show ((720175851743 / 500000000000) : ℝ) = ((500000000000 / 720175851743) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10516_neg : (366710993 / 1000000000) ≤ -Real.log (31250000000 / 45093150859) ∧
    -Real.log (31250000000 / 45093150859) ≤ (183355497 / 500000000) := by
  have h := checkLog_sound (w := (13843150859 / 76343150859)) (n := 12)
    (lo := (366710993 / 1000000000)) (hi := (183355497 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45093150859 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45093150859 / 31250000000) = 1/(31250000000 / 45093150859) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10516 : Bounds (366710993 / 1000000000) (183355497 / 500000000) (Real.log (45093150859 / 31250000000)) := by
  have h := reflection_log_10516_neg
  have he : Real.log (45093150859 / 31250000000) = -Real.log (31250000000 / 45093150859) := by
    rw [show ((45093150859 / 31250000000) : ℝ) = ((31250000000 / 45093150859) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10517_neg : (737733333 / 1000000000) ≤ -Real.log (100000000000 / 209119010819) ∧
    -Real.log (100000000000 / 209119010819) ≤ (147546667 / 200000000) := by
  have h := checkLog_sound (w := (9119010819 / 409119010819)) (n := 12)
    (lo := (44586153 / 1000000000)) (hi := (22293077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((209119010819 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(209119010819 / 200000000000) = 1/(100000000000 / 209119010819) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10517 : Bounds (737733333 / 1000000000) (147546667 / 200000000) (Real.log (209119010819 / 100000000000)) := by
  have h := reflection_log_10517_neg
  have he : Real.log (209119010819 / 100000000000) = -Real.log (100000000000 / 209119010819) := by
    rw [show ((209119010819 / 100000000000) : ℝ) = ((100000000000 / 209119010819) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10518_neg : (740018949 / 1000000000) ≤ -Real.log (5000000000 / 10479876161) ∧
    -Real.log (5000000000 / 10479876161) ≤ (740018951 / 1000000000) := by
  have h := checkLog_sound (w := (479876161 / 20479876161)) (n := 12)
    (lo := (46871769 / 1000000000)) (hi := (4687177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10479876161 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10479876161 / 10000000000) = 1/(5000000000 / 10479876161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10518 : Bounds (740018949 / 1000000000) (740018951 / 1000000000) (Real.log (10479876161 / 5000000000)) := by
  have h := reflection_log_10518_neg
  have he : Real.log (10479876161 / 5000000000) = -Real.log (5000000000 / 10479876161) := by
    rw [show ((10479876161 / 5000000000) : ℝ) = ((5000000000 / 10479876161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10519_neg : (151900727 / 500000000) ≤ -Real.log (200 / 271) ∧
    -Real.log (200 / 271) ≤ (60760291 / 200000000) := by
  have h := checkLog_sound (w := (71 / 471)) (n := 12)
    (lo := (151900727 / 500000000)) (hi := (60760291 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((271 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(271 / 200) = 1/(200 / 271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10519 : Bounds (151900727 / 500000000) (60760291 / 200000000) (Real.log (271 / 200)) := by
  have h := reflection_log_10519_neg
  have he : Real.log (271 / 200) = -Real.log (200 / 271) := by
    rw [show ((271 / 200) : ℝ) = ((200 / 271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10520_neg : (219252481 / 500000000) ≤ -Real.log (129 / 200) ∧
    -Real.log (129 / 200) ≤ (438504963 / 1000000000) := by
  have h := checkLog_sound (w := (71 / 329)) (n := 12)
    (lo := (219252481 / 500000000)) (hi := (438504963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200 / 129) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200 / 129) = 1/(129 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10520 : Bounds (-438504963 / 1000000000) (-219252481 / 500000000) (Real.log (129 / 200)) := by
  have h := reflection_log_10520_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10521_neg : (354937 / 1000000000) ≤ -Real.log (200000 / 200071) ∧
    -Real.log (200000 / 200071) ≤ (177469 / 500000000) := by
  have h := checkLog_sound (w := (71 / 400071)) (n := 12)
    (lo := (354937 / 1000000000)) (hi := (177469 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200071 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200071 / 200000) = 1/(200000 / 200071) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10521 : Bounds (354937 / 1000000000) (177469 / 500000000) (Real.log (200071 / 200000)) := by
  have h := reflection_log_10521_neg
  have he : Real.log (200071 / 200000) = -Real.log (200000 / 200071) := by
    rw [show ((200071 / 200000) : ℝ) = ((200000 / 200071) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10522_neg : (355063 / 1000000000) ≤ -Real.log (199929 / 200000) ∧
    -Real.log (199929 / 200000) ≤ (44383 / 125000000) := by
  have h := checkLog_sound (w := (71 / 399929)) (n := 12)
    (lo := (355063 / 1000000000)) (hi := (44383 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199929) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199929) = 1/(199929 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10522 : Bounds (-44383 / 125000000) (-355063 / 1000000000) (Real.log (199929 / 200000)) := by
  have h := reflection_log_10522_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10523_neg : (33269259 / 200000000) ≤ -Real.log (500000 / 590491) ∧
    -Real.log (500000 / 590491) ≤ (20793287 / 125000000) := by
  have h := checkLog_sound (w := (90491 / 1090491)) (n := 12)
    (lo := (33269259 / 200000000)) (hi := (20793287 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((590491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(590491 / 500000) = 1/(500000 / 590491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10523 : Bounds (33269259 / 200000000) (20793287 / 125000000) (Real.log (590491 / 500000)) := by
  have h := reflection_log_10523_neg
  have he : Real.log (590491 / 500000) = -Real.log (500000 / 590491) := by
    rw [show ((590491 / 500000) : ℝ) = ((500000 / 590491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10524_neg : (199649217 / 1000000000) ≤ -Real.log (409509 / 500000) ∧
    -Real.log (409509 / 500000) ≤ (99824609 / 500000000) := by
  have h := checkLog_sound (w := (90491 / 909509)) (n := 12)
    (lo := (199649217 / 1000000000)) (hi := (99824609 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 409509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 409509) = 1/(409509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10524 : Bounds (-99824609 / 500000000) (-199649217 / 1000000000) (Real.log (409509 / 500000)) := by
  have h := reflection_log_10524_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10525_neg : (167093699 / 1000000000) ≤ -Real.log (200000 / 236373) ∧
    -Real.log (200000 / 236373) ≤ (1670937 / 10000000) := by
  have h := checkLog_sound (w := (36373 / 436373)) (n := 12)
    (lo := (167093699 / 1000000000)) (hi := (1670937 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((236373 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(236373 / 200000) = 1/(200000 / 236373) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10525 : Bounds (167093699 / 1000000000) (1670937 / 10000000) (Real.log (236373 / 200000)) := by
  have h := reflection_log_10525_neg
  have he : Real.log (236373 / 200000) = -Real.log (200000 / 236373) := by
    rw [show ((236373 / 200000) : ℝ) = ((200000 / 236373) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10526_neg : (200727919 / 1000000000) ≤ -Real.log (163627 / 200000) ∧
    -Real.log (163627 / 200000) ≤ (2509099 / 12500000) := by
  have h := checkLog_sound (w := (36373 / 363627)) (n := 12)
    (lo := (200727919 / 1000000000)) (hi := (2509099 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 163627) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 163627) = 1/(163627 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10526 : Bounds (-2509099 / 12500000) (-200727919 / 1000000000) (Real.log (163627 / 200000)) := by
  have h := reflection_log_10526_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10527_neg : (1681711 / 50000000) ≤ -Real.log (38677004871 / 40000000000) ∧
    -Real.log (38677004871 / 40000000000) ≤ (33634221 / 1000000000) := by
  have h := checkLog_sound (w := (1322995129 / 78677004871)) (n := 12)
    (lo := (1681711 / 50000000)) (hi := (33634221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 38677004871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 38677004871) = 1/(38677004871 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10527 : Bounds (-33634221 / 1000000000) (-1681711 / 50000000) (Real.log (38677004871 / 40000000000)) := by
  have h := reflection_log_10527_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10528_neg : (33302921 / 1000000000) ≤ -Real.log (241811378919 / 250000000000) ∧
    -Real.log (241811378919 / 250000000000) ≤ (16651461 / 500000000) := by
  have h := checkLog_sound (w := (8188621081 / 491811378919)) (n := 12)
    (lo := (33302921 / 1000000000)) (hi := (16651461 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241811378919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241811378919) = 1/(241811378919 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10528 : Bounds (-16651461 / 500000000) (-33302921 / 1000000000) (Real.log (241811378919 / 250000000000)) := by
  have h := reflection_log_10528_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10529_neg : (365995513 / 1000000000) ≤ -Real.log (500000000000 / 720974386399) ∧
    -Real.log (500000000000 / 720974386399) ≤ (182997757 / 500000000) := by
  have h := checkLog_sound (w := (220974386399 / 1220974386399)) (n := 12)
    (lo := (365995513 / 1000000000)) (hi := (182997757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((720974386399 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(720974386399 / 500000000000) = 1/(500000000000 / 720974386399) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10529 : Bounds (365995513 / 1000000000) (182997757 / 500000000) (Real.log (720974386399 / 500000000000)) := by
  have h := reflection_log_10529_neg
  have he : Real.log (720974386399 / 500000000000) = -Real.log (500000000000 / 720974386399) := by
    rw [show ((720974386399 / 500000000000) : ℝ) = ((500000000000 / 720974386399) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10530_neg : (183910809 / 500000000) ≤ -Real.log (500000000000 / 722292164497) ∧
    -Real.log (500000000000 / 722292164497) ≤ (367821619 / 1000000000) := by
  have h := checkLog_sound (w := (222292164497 / 1222292164497)) (n := 12)
    (lo := (183910809 / 500000000)) (hi := (367821619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((722292164497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(722292164497 / 500000000000) = 1/(500000000000 / 722292164497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10530 : Bounds (183910809 / 500000000) (367821619 / 1000000000) (Real.log (722292164497 / 500000000000)) := by
  have h := reflection_log_10530_neg
  have he : Real.log (722292164497 / 500000000000) = -Real.log (500000000000 / 722292164497) := by
    rw [show ((722292164497 / 500000000000) : ℝ) = ((500000000000 / 722292164497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10531_neg : (740018949 / 1000000000) ≤ -Real.log (500000000000 / 1047987616099) ∧
    -Real.log (500000000000 / 1047987616099) ≤ (740018951 / 1000000000) := by
  have h := checkLog_sound (w := (47987616099 / 2047987616099)) (n := 12)
    (lo := (46871769 / 1000000000)) (hi := (4687177 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1047987616099 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1047987616099 / 1000000000000) = 1/(500000000000 / 1047987616099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10531 : Bounds (740018949 / 1000000000) (740018951 / 1000000000) (Real.log (1047987616099 / 500000000000)) := by
  have h := reflection_log_10531_neg
  have he : Real.log (1047987616099 / 500000000000) = -Real.log (500000000000 / 1047987616099) := by
    rw [show ((1047987616099 / 500000000000) : ℝ) = ((500000000000 / 1047987616099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10532_neg : (148461283 / 200000000) ≤ -Real.log (5000000000 / 10503875969) ∧
    -Real.log (5000000000 / 10503875969) ≤ (742306417 / 1000000000) := by
  have h := checkLog_sound (w := (503875969 / 20503875969)) (n := 12)
    (lo := (9831847 / 200000000)) (hi := (12289809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10503875969 / 10000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(10503875969 / 10000000000) = 1/(5000000000 / 10503875969) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10532 : Bounds (148461283 / 200000000) (742306417 / 1000000000) (Real.log (10503875969 / 5000000000)) := by
  have h := reflection_log_10532_neg
  have he : Real.log (10503875969 / 5000000000) = -Real.log (5000000000 / 10503875969) := by
    rw [show ((10503875969 / 5000000000) : ℝ) = ((5000000000 / 10503875969) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10533_neg : (304539189 / 1000000000) ≤ -Real.log (250 / 339) ∧
    -Real.log (250 / 339) ≤ (30453919 / 100000000) := by
  have h := checkLog_sound (w := (89 / 589)) (n := 12)
    (lo := (304539189 / 1000000000)) (hi := (30453919 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((339 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(339 / 250) = 1/(250 / 339) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10533 : Bounds (304539189 / 1000000000) (30453919 / 100000000) (Real.log (339 / 250)) := by
  have h := reflection_log_10533_neg
  have he : Real.log (339 / 250) = -Real.log (250 / 339) := by
    rw [show ((339 / 250) : ℝ) = ((250 / 339) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10534_neg : (55007069 / 125000000) ≤ -Real.log (161 / 250) ∧
    -Real.log (161 / 250) ≤ (440056553 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 411)) (n := 12)
    (lo := (55007069 / 125000000)) (hi := (440056553 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250 / 161) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250 / 161) = 1/(161 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10534 : Bounds (-440056553 / 1000000000) (-55007069 / 125000000) (Real.log (161 / 250)) := by
  have h := reflection_log_10534_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10535_neg : (11123 / 31250000) ≤ -Real.log (250000 / 250089) ∧
    -Real.log (250000 / 250089) ≤ (355937 / 1000000000) := by
  have h := checkLog_sound (w := (89 / 500089)) (n := 12)
    (lo := (11123 / 31250000)) (hi := (355937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250089 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250089 / 250000) = 1/(250000 / 250089) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10535 : Bounds (11123 / 31250000) (355937 / 1000000000) (Real.log (250089 / 250000)) := by
  have h := reflection_log_10535_neg
  have he : Real.log (250089 / 250000) = -Real.log (250000 / 250089) := by
    rw [show ((250089 / 250000) : ℝ) = ((250000 / 250089) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10536_neg : (356063 / 1000000000) ≤ -Real.log (249911 / 250000) ∧
    -Real.log (249911 / 250000) ≤ (11127 / 31250000) := by
  have h := checkLog_sound (w := (89 / 499911)) (n := 12)
    (lo := (356063 / 1000000000)) (hi := (11127 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249911) = 1/(249911 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10536 : Bounds (-11127 / 31250000) (-356063 / 1000000000) (Real.log (249911 / 250000)) := by
  have h := reflection_log_10536_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10537_neg : (83399603 / 500000000) ≤ -Real.log (1000000 / 1181517) ∧
    -Real.log (1000000 / 1181517) ≤ (166799207 / 1000000000) := by
  have h := checkLog_sound (w := (181517 / 2181517)) (n := 12)
    (lo := (83399603 / 500000000)) (hi := (166799207 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1181517 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1181517 / 1000000) = 1/(1000000 / 1181517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10537 : Bounds (83399603 / 500000000) (166799207 / 1000000000) (Real.log (1181517 / 1000000)) := by
  have h := reflection_log_10537_neg
  have he : Real.log (1181517 / 1000000) = -Real.log (1000000 / 1181517) := by
    rw [show ((1181517 / 1000000) : ℝ) = ((1000000 / 1181517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10538_neg : (50075663 / 250000000) ≤ -Real.log (818483 / 1000000) ∧
    -Real.log (818483 / 1000000) ≤ (200302653 / 1000000000) := by
  have h := checkLog_sound (w := (181517 / 1818483)) (n := 12)
    (lo := (50075663 / 250000000)) (hi := (200302653 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 818483) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 818483) = 1/(818483 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10538 : Bounds (-200302653 / 1000000000) (-50075663 / 250000000) (Real.log (818483 / 1000000)) := by
  have h := reflection_log_10538_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10539_neg : (83773981 / 500000000) ≤ -Real.log (500000 / 591201) ∧
    -Real.log (500000 / 591201) ≤ (167547963 / 1000000000) := by
  have h := checkLog_sound (w := (91201 / 1091201)) (n := 12)
    (lo := (83773981 / 500000000)) (hi := (167547963 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591201 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591201 / 500000) = 1/(500000 / 591201) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10539 : Bounds (83773981 / 500000000) (167547963 / 1000000000) (Real.log (591201 / 500000)) := by
  have h := reflection_log_10539_neg
  have he : Real.log (591201 / 500000) = -Real.log (500000 / 591201) := by
    rw [show ((591201 / 500000) : ℝ) = ((500000 / 591201) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10540_neg : (40276901 / 200000000) ≤ -Real.log (408799 / 500000) ∧
    -Real.log (408799 / 500000) ≤ (100692253 / 500000000) := by
  have h := checkLog_sound (w := (91201 / 908799)) (n := 12)
    (lo := (40276901 / 200000000)) (hi := (100692253 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408799) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408799) = 1/(408799 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10540 : Bounds (-100692253 / 500000000) (-40276901 / 200000000) (Real.log (408799 / 500000)) := by
  have h := reflection_log_10540_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10541_neg : (33836543 / 1000000000) ≤ -Real.log (241682377599 / 250000000000) ∧
    -Real.log (241682377599 / 250000000000) ≤ (66087 / 1953125) := by
  have h := checkLog_sound (w := (8317622401 / 491682377599)) (n := 12)
    (lo := (33836543 / 1000000000)) (hi := (66087 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241682377599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241682377599) = 1/(241682377599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10541 : Bounds (-66087 / 1953125) (-33836543 / 1000000000) (Real.log (241682377599 / 250000000000)) := by
  have h := reflection_log_10541_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10542_neg : (16751723 / 500000000) ≤ -Real.log (967051578711 / 1000000000000) ∧
    -Real.log (967051578711 / 1000000000000) ≤ (33503447 / 1000000000) := by
  have h := checkLog_sound (w := (32948421289 / 1967051578711)) (n := 12)
    (lo := (16751723 / 500000000)) (hi := (33503447 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 967051578711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 967051578711) = 1/(967051578711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10542 : Bounds (-33503447 / 1000000000) (-16751723 / 500000000) (Real.log (967051578711 / 1000000000000)) := by
  have h := reflection_log_10542_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10543_neg : (183550929 / 500000000) ≤ -Real.log (500000000000 / 721772474199) ∧
    -Real.log (500000000000 / 721772474199) ≤ (367101859 / 1000000000) := by
  have h := checkLog_sound (w := (221772474199 / 1221772474199)) (n := 12)
    (lo := (183550929 / 500000000)) (hi := (367101859 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((721772474199 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(721772474199 / 500000000000) = 1/(500000000000 / 721772474199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10543 : Bounds (183550929 / 500000000) (367101859 / 1000000000) (Real.log (721772474199 / 500000000000)) := by
  have h := reflection_log_10543_neg
  have he : Real.log (721772474199 / 500000000000) = -Real.log (500000000000 / 721772474199) := by
    rw [show ((721772474199 / 500000000000) : ℝ) = ((500000000000 / 721772474199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10544_neg : (92233117 / 250000000) ≤ -Real.log (31250000000 / 45193435527) ∧
    -Real.log (31250000000 / 45193435527) ≤ (368932469 / 1000000000) := by
  have h := checkLog_sound (w := (13943435527 / 76443435527)) (n := 12)
    (lo := (92233117 / 250000000)) (hi := (368932469 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((45193435527 / 31250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(45193435527 / 31250000000) = 1/(31250000000 / 45193435527) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10544 : Bounds (92233117 / 250000000) (368932469 / 1000000000) (Real.log (45193435527 / 31250000000)) := by
  have h := reflection_log_10544_neg
  have he : Real.log (45193435527 / 31250000000) = -Real.log (31250000000 / 45193435527) := by
    rw [show ((45193435527 / 31250000000) : ℝ) = ((31250000000 / 45193435527) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10545_neg : (148461283 / 200000000) ≤ -Real.log (500000000000 / 1050387596899) ∧
    -Real.log (500000000000 / 1050387596899) ≤ (742306417 / 1000000000) := by
  have h := checkLog_sound (w := (50387596899 / 2050387596899)) (n := 12)
    (lo := (9831847 / 200000000)) (hi := (12289809 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1050387596899 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1050387596899 / 1000000000000) = 1/(500000000000 / 1050387596899) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10545 : Bounds (148461283 / 200000000) (742306417 / 1000000000) (Real.log (1050387596899 / 500000000000)) := by
  have h := reflection_log_10545_neg
  have he : Real.log (1050387596899 / 500000000000) = -Real.log (500000000000 / 1050387596899) := by
    rw [show ((1050387596899 / 500000000000) : ℝ) = ((500000000000 / 1050387596899) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10546_neg : (744595741 / 1000000000) ≤ -Real.log (31250000000 / 65799689441) ∧
    -Real.log (31250000000 / 65799689441) ≤ (744595743 / 1000000000) := by
  have h := checkLog_sound (w := (3299689441 / 128299689441)) (n := 12)
    (lo := (51448561 / 1000000000)) (hi := (25724281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((65799689441 / 62500000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(65799689441 / 62500000000) = 1/(31250000000 / 65799689441) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10546 : Bounds (744595741 / 1000000000) (744595743 / 1000000000) (Real.log (65799689441 / 31250000000)) := by
  have h := reflection_log_10546_neg
  have he : Real.log (65799689441 / 31250000000) = -Real.log (31250000000 / 65799689441) := by
    rw [show ((65799689441 / 31250000000) : ℝ) = ((31250000000 / 65799689441) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10547_neg : (15263819 / 50000000) ≤ -Real.log (1000 / 1357) ∧
    -Real.log (1000 / 1357) ≤ (305276381 / 1000000000) := by
  have h := checkLog_sound (w := (357 / 2357)) (n := 12)
    (lo := (15263819 / 50000000)) (hi := (305276381 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1357 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1357 / 1000) = 1/(1000 / 1357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10547 : Bounds (15263819 / 50000000) (305276381 / 1000000000) (Real.log (1357 / 1000)) := by
  have h := reflection_log_10547_neg
  have he : Real.log (1357 / 1000) = -Real.log (1000 / 1357) := by
    rw [show ((1357 / 1000) : ℝ) = ((1000 / 1357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10548_neg : (220805277 / 500000000) ≤ -Real.log (643 / 1000) ∧
    -Real.log (643 / 1000) ≤ (88322111 / 200000000) := by
  have h := checkLog_sound (w := (357 / 1643)) (n := 12)
    (lo := (220805277 / 500000000)) (hi := (88322111 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 643) = 1/(643 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10548 : Bounds (-88322111 / 200000000) (-220805277 / 500000000) (Real.log (643 / 1000)) := by
  have h := reflection_log_10548_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10549_neg : (44617 / 125000000) ≤ -Real.log (1000000 / 1000357) ∧
    -Real.log (1000000 / 1000357) ≤ (356937 / 1000000000) := by
  have h := checkLog_sound (w := (357 / 2000357)) (n := 12)
    (lo := (44617 / 125000000)) (hi := (356937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000357 / 1000000) = 1/(1000000 / 1000357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10549 : Bounds (44617 / 125000000) (356937 / 1000000000) (Real.log (1000357 / 1000000)) := by
  have h := reflection_log_10549_neg
  have he : Real.log (1000357 / 1000000) = -Real.log (1000000 / 1000357) := by
    rw [show ((1000357 / 1000000) : ℝ) = ((1000000 / 1000357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10550_neg : (357063 / 1000000000) ≤ -Real.log (999643 / 1000000) ∧
    -Real.log (999643 / 1000000) ≤ (44633 / 125000000) := by
  have h := checkLog_sound (w := (357 / 1999643)) (n := 12)
    (lo := (357063 / 1000000000)) (hi := (44633 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999643) = 1/(999643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10550 : Bounds (-44633 / 125000000) (-357063 / 1000000000) (Real.log (999643 / 1000000)) := by
  have h := reflection_log_10550_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10551_neg : (167252757 / 1000000000) ≤ -Real.log (1000000 / 1182053) ∧
    -Real.log (1000000 / 1182053) ≤ (83626379 / 500000000) := by
  have h := checkLog_sound (w := (182053 / 2182053)) (n := 12)
    (lo := (167252757 / 1000000000)) (hi := (83626379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182053 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182053 / 1000000) = 1/(1000000 / 1182053) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10551 : Bounds (167252757 / 1000000000) (83626379 / 500000000) (Real.log (1182053 / 1000000)) := by
  have h := reflection_log_10551_neg
  have he : Real.log (1182053 / 1000000) = -Real.log (1000000 / 1182053) := by
    rw [show ((1182053 / 1000000) : ℝ) = ((1000000 / 1182053) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10552_neg : (25119717 / 125000000) ≤ -Real.log (817947 / 1000000) ∧
    -Real.log (817947 / 1000000) ≤ (200957737 / 1000000000) := by
  have h := checkLog_sound (w := (182053 / 1817947)) (n := 12)
    (lo := (25119717 / 125000000)) (hi := (200957737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817947) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817947) = 1/(817947 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10552 : Bounds (-200957737 / 1000000000) (-25119717 / 125000000) (Real.log (817947 / 1000000)) := by
  have h := reflection_log_10552_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10553_neg : (168002019 / 1000000000) ≤ -Real.log (1000000 / 1182939) ∧
    -Real.log (1000000 / 1182939) ≤ (8400101 / 50000000) := by
  have h := checkLog_sound (w := (182939 / 2182939)) (n := 12)
    (lo := (168002019 / 1000000000)) (hi := (8400101 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1182939 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1182939 / 1000000) = 1/(1000000 / 1182939) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10553 : Bounds (168002019 / 1000000000) (8400101 / 50000000) (Real.log (1182939 / 1000000)) := by
  have h := reflection_log_10553_neg
  have he : Real.log (1182939 / 1000000) = -Real.log (1000000 / 1182939) := by
    rw [show ((1182939 / 1000000) : ℝ) = ((1000000 / 1182939) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10554_neg : (202041523 / 1000000000) ≤ -Real.log (817061 / 1000000) ∧
    -Real.log (817061 / 1000000) ≤ (50510381 / 250000000) := by
  have h := checkLog_sound (w := (182939 / 1817061)) (n := 12)
    (lo := (202041523 / 1000000000)) (hi := (50510381 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 817061) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 817061) = 1/(817061 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10554 : Bounds (-50510381 / 250000000) (-202041523 / 1000000000) (Real.log (817061 / 1000000)) := by
  have h := reflection_log_10554_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10555_neg : (34039503 / 1000000000) ≤ -Real.log (966533322279 / 1000000000000) ∧
    -Real.log (966533322279 / 1000000000000) ≤ (2127469 / 62500000) := by
  have h := checkLog_sound (w := (33466677721 / 1966533322279)) (n := 12)
    (lo := (34039503 / 1000000000)) (hi := (2127469 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966533322279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966533322279) = 1/(966533322279 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10555 : Bounds (-2127469 / 62500000) (-34039503 / 1000000000) (Real.log (966533322279 / 1000000000000)) := by
  have h := reflection_log_10555_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10556_neg : (33704979 / 1000000000) ≤ -Real.log (966856705191 / 1000000000000) ∧
    -Real.log (966856705191 / 1000000000000) ≤ (1685249 / 50000000) := by
  have h := checkLog_sound (w := (33143294809 / 1966856705191)) (n := 12)
    (lo := (33704979 / 1000000000)) (hi := (1685249 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966856705191) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966856705191) = 1/(966856705191 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10556 : Bounds (-1685249 / 50000000) (-33704979 / 1000000000) (Real.log (966856705191 / 1000000000000)) := by
  have h := reflection_log_10556_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10557_neg : (368210493 / 1000000000) ≤ -Real.log (250000000000 / 361286550351) ∧
    -Real.log (250000000000 / 361286550351) ≤ (184105247 / 500000000) := by
  have h := checkLog_sound (w := (111286550351 / 611286550351)) (n := 12)
    (lo := (368210493 / 1000000000)) (hi := (184105247 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((361286550351 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(361286550351 / 250000000000) = 1/(250000000000 / 361286550351) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10557 : Bounds (368210493 / 1000000000) (184105247 / 500000000) (Real.log (361286550351 / 250000000000)) := by
  have h := reflection_log_10557_neg
  have he : Real.log (361286550351 / 250000000000) = -Real.log (250000000000 / 361286550351) := by
    rw [show ((361286550351 / 250000000000) : ℝ) = ((250000000000 / 361286550351) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10558_neg : (370043543 / 1000000000) ≤ -Real.log (125000000000 / 180974706907) ∧
    -Real.log (125000000000 / 180974706907) ≤ (46255443 / 125000000) := by
  have h := checkLog_sound (w := (55974706907 / 305974706907)) (n := 12)
    (lo := (370043543 / 1000000000)) (hi := (46255443 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((180974706907 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(180974706907 / 125000000000) = 1/(125000000000 / 180974706907) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10558 : Bounds (370043543 / 1000000000) (46255443 / 125000000) (Real.log (180974706907 / 125000000000)) := by
  have h := reflection_log_10558_neg
  have he : Real.log (180974706907 / 125000000000) = -Real.log (125000000000 / 180974706907) := by
    rw [show ((180974706907 / 125000000000) : ℝ) = ((125000000000 / 180974706907) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10559_neg : (744595741 / 1000000000) ≤ -Real.log (100000000000 / 210559006211) ∧
    -Real.log (100000000000 / 210559006211) ≤ (744595743 / 1000000000) := by
  have h := checkLog_sound (w := (10559006211 / 410559006211)) (n := 12)
    (lo := (51448561 / 1000000000)) (hi := (25724281 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((210559006211 / 200000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(210559006211 / 200000000000) = 1/(100000000000 / 210559006211) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10559 : Bounds (744595741 / 1000000000) (744595743 / 1000000000) (Real.log (210559006211 / 100000000000)) := by
  have h := reflection_log_10559_neg
  have he : Real.log (210559006211 / 100000000000) = -Real.log (100000000000 / 210559006211) := by
    rw [show ((210559006211 / 100000000000) : ℝ) = ((100000000000 / 210559006211) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0165 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_10560_neg : (149377387 / 200000000) ≤ -Real.log (7812500000 / 16487655521) ∧
    -Real.log (7812500000 / 16487655521) ≤ (746886937 / 1000000000) := by
  have h := checkLog_sound (w := (862655521 / 32112655521)) (n := 12)
    (lo := (10747951 / 200000000)) (hi := (13434939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16487655521 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16487655521 / 15625000000) = 1/(7812500000 / 16487655521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10560 : Bounds (149377387 / 200000000) (746886937 / 1000000000) (Real.log (16487655521 / 7812500000)) := by
  have h := reflection_log_10560_neg
  have he : Real.log (16487655521 / 7812500000) = -Real.log (7812500000 / 16487655521) := by
    rw [show ((16487655521 / 7812500000) : ℝ) = ((7812500000 / 16487655521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10561_neg : (306013029 / 1000000000) ≤ -Real.log (500 / 679) ∧
    -Real.log (500 / 679) ≤ (30601303 / 100000000) := by
  have h := checkLog_sound (w := (179 / 1179)) (n := 12)
    (lo := (306013029 / 1000000000)) (hi := (30601303 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((679 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(679 / 500) = 1/(500 / 679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10561 : Bounds (306013029 / 1000000000) (30601303 / 100000000) (Real.log (679 / 500)) := by
  have h := reflection_log_10561_neg
  have he : Real.log (679 / 500) = -Real.log (500 / 679) := by
    rw [show ((679 / 500) : ℝ) = ((500 / 679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10562_neg : (17726679 / 40000000) ≤ -Real.log (321 / 500) ∧
    -Real.log (321 / 500) ≤ (1731121 / 3906250) := by
  have h := checkLog_sound (w := (179 / 821)) (n := 12)
    (lo := (17726679 / 40000000)) (hi := (1731121 / 3906250))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 321) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 321) = 1/(321 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10562 : Bounds (-1731121 / 3906250) (-17726679 / 40000000) (Real.log (321 / 500)) := by
  have h := reflection_log_10562_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10563_neg : (71587 / 200000000) ≤ -Real.log (500000 / 500179) ∧
    -Real.log (500000 / 500179) ≤ (22371 / 62500000) := by
  have h := checkLog_sound (w := (179 / 1000179)) (n := 12)
    (lo := (71587 / 200000000)) (hi := (22371 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500179 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500179 / 500000) = 1/(500000 / 500179) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10563 : Bounds (71587 / 200000000) (22371 / 62500000) (Real.log (500179 / 500000)) := by
  have h := reflection_log_10563_neg
  have he : Real.log (500179 / 500000) = -Real.log (500000 / 500179) := by
    rw [show ((500179 / 500000) : ℝ) = ((500000 / 500179) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10564_neg : (22379 / 62500000) ≤ -Real.log (499821 / 500000) ∧
    -Real.log (499821 / 500000) ≤ (71613 / 200000000) := by
  have h := checkLog_sound (w := (179 / 999821)) (n := 12)
    (lo := (22379 / 62500000)) (hi := (71613 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499821) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499821) = 1/(499821 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10564 : Bounds (-71613 / 200000000) (-22379 / 62500000) (Real.log (499821 / 500000)) := by
  have h := reflection_log_10564_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10565_neg : (41926737 / 250000000) ≤ -Real.log (100000 / 118259) ∧
    -Real.log (100000 / 118259) ≤ (167706949 / 1000000000) := by
  have h := checkLog_sound (w := (18259 / 218259)) (n := 12)
    (lo := (41926737 / 250000000)) (hi := (167706949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118259 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118259 / 100000) = 1/(100000 / 118259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10565 : Bounds (41926737 / 250000000) (167706949 / 1000000000) (Real.log (118259 / 100000)) := by
  have h := reflection_log_10565_neg
  have he : Real.log (118259 / 100000) = -Real.log (100000 / 118259) := by
    rw [show ((118259 / 100000) : ℝ) = ((100000 / 118259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10566_neg : (100807237 / 500000000) ≤ -Real.log (81741 / 100000) ∧
    -Real.log (81741 / 100000) ≤ (8064579 / 40000000) := by
  have h := checkLog_sound (w := (18259 / 181741)) (n := 12)
    (lo := (100807237 / 500000000)) (hi := (8064579 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81741) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81741) = 1/(81741 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10566 : Bounds (-8064579 / 40000000) (-100807237 / 500000000) (Real.log (81741 / 100000)) := by
  have h := reflection_log_10566_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10567_neg : (16845587 / 100000000) ≤ -Real.log (250000 / 295869) ∧
    -Real.log (250000 / 295869) ≤ (168455871 / 1000000000) := by
  have h := checkLog_sound (w := (45869 / 545869)) (n := 12)
    (lo := (16845587 / 100000000)) (hi := (168455871 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((295869 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(295869 / 250000) = 1/(250000 / 295869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10567 : Bounds (16845587 / 100000000) (168455871 / 1000000000) (Real.log (295869 / 250000)) := by
  have h := reflection_log_10567_neg
  have he : Real.log (295869 / 250000) = -Real.log (250000 / 295869) := by
    rw [show ((295869 / 250000) : ℝ) = ((250000 / 295869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10568_neg : (202698973 / 1000000000) ≤ -Real.log (204131 / 250000) ∧
    -Real.log (204131 / 250000) ≤ (101349487 / 500000000) := by
  have h := checkLog_sound (w := (45869 / 454131)) (n := 12)
    (lo := (202698973 / 1000000000)) (hi := (101349487 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 204131) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 204131) = 1/(204131 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10568 : Bounds (-101349487 / 500000000) (-202698973 / 1000000000) (Real.log (204131 / 250000)) := by
  have h := reflection_log_10568_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10569_neg : (17121551 / 500000000) ≤ -Real.log (60396034839 / 62500000000) ∧
    -Real.log (60396034839 / 62500000000) ≤ (34243103 / 1000000000) := by
  have h := checkLog_sound (w := (2103965161 / 122896034839)) (n := 12)
    (lo := (17121551 / 500000000)) (hi := (34243103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60396034839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60396034839) = 1/(60396034839 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10569 : Bounds (-34243103 / 1000000000) (-17121551 / 500000000) (Real.log (60396034839 / 62500000000)) := by
  have h := reflection_log_10569_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10570_neg : (1356301 / 40000000) ≤ -Real.log (9666608919 / 10000000000) ∧
    -Real.log (9666608919 / 10000000000) ≤ (16953763 / 500000000) := by
  have h := checkLog_sound (w := (333391081 / 19666608919)) (n := 12)
    (lo := (1356301 / 40000000)) (hi := (16953763 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9666608919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9666608919) = 1/(9666608919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10570 : Bounds (-16953763 / 500000000) (-1356301 / 40000000) (Real.log (9666608919 / 10000000000)) := by
  have h := reflection_log_10570_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10571_neg : (184660711 / 500000000) ≤ -Real.log (6250000000 / 9042203423) ∧
    -Real.log (6250000000 / 9042203423) ≤ (369321423 / 1000000000) := by
  have h := checkLog_sound (w := (2792203423 / 15292203423)) (n := 12)
    (lo := (184660711 / 500000000)) (hi := (369321423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9042203423 / 6250000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9042203423 / 6250000000) = 1/(6250000000 / 9042203423) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10571 : Bounds (184660711 / 500000000) (369321423 / 1000000000) (Real.log (9042203423 / 6250000000)) := by
  have h := reflection_log_10571_neg
  have he : Real.log (9042203423 / 6250000000) = -Real.log (6250000000 / 9042203423) := by
    rw [show ((9042203423 / 6250000000) : ℝ) = ((6250000000 / 9042203423) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10572_neg : (92788711 / 250000000) ≤ -Real.log (100000000000 / 144940748833) ∧
    -Real.log (100000000000 / 144940748833) ≤ (74230969 / 200000000) := by
  have h := checkLog_sound (w := (44940748833 / 244940748833)) (n := 12)
    (lo := (92788711 / 250000000)) (hi := (74230969 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((144940748833 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(144940748833 / 100000000000) = 1/(100000000000 / 144940748833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10572 : Bounds (92788711 / 250000000) (74230969 / 200000000) (Real.log (144940748833 / 100000000000)) := by
  have h := reflection_log_10572_neg
  have he : Real.log (144940748833 / 100000000000) = -Real.log (100000000000 / 144940748833) := by
    rw [show ((144940748833 / 100000000000) : ℝ) = ((100000000000 / 144940748833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10573_neg : (149377387 / 200000000) ≤ -Real.log (500000000000 / 1055209953343) ∧
    -Real.log (500000000000 / 1055209953343) ≤ (746886937 / 1000000000) := by
  have h := checkLog_sound (w := (55209953343 / 2055209953343)) (n := 12)
    (lo := (10747951 / 200000000)) (hi := (13434939 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1055209953343 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1055209953343 / 1000000000000) = 1/(500000000000 / 1055209953343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10573 : Bounds (149377387 / 200000000) (746886937 / 1000000000) (Real.log (1055209953343 / 500000000000)) := by
  have h := reflection_log_10573_neg
  have he : Real.log (1055209953343 / 500000000000) = -Real.log (500000000000 / 1055209953343) := by
    rw [show ((1055209953343 / 500000000000) : ℝ) = ((500000000000 / 1055209953343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10574_neg : (749180003 / 1000000000) ≤ -Real.log (250000000000 / 528816199377) ∧
    -Real.log (250000000000 / 528816199377) ≤ (149836001 / 200000000) := by
  have h := checkLog_sound (w := (28816199377 / 1028816199377)) (n := 12)
    (lo := (56032823 / 1000000000)) (hi := (7004103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((528816199377 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(528816199377 / 500000000000) = 1/(250000000000 / 528816199377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10574 : Bounds (749180003 / 1000000000) (149836001 / 200000000) (Real.log (528816199377 / 250000000000)) := by
  have h := reflection_log_10574_neg
  have he : Real.log (528816199377 / 250000000000) = -Real.log (250000000000 / 528816199377) := by
    rw [show ((528816199377 / 250000000000) : ℝ) = ((250000000000 / 528816199377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10575_neg : (61349827 / 200000000) ≤ -Real.log (1000 / 1359) ∧
    -Real.log (1000 / 1359) ≤ (19171821 / 62500000) := by
  have h := checkLog_sound (w := (359 / 2359)) (n := 12)
    (lo := (61349827 / 200000000)) (hi := (19171821 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1359 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1359 / 1000) = 1/(1000 / 1359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10575 : Bounds (61349827 / 200000000) (19171821 / 62500000) (Real.log (1359 / 1000)) := by
  have h := reflection_log_10575_neg
  have he : Real.log (1359 / 1000) = -Real.log (1000 / 1359) := by
    rw [show ((1359 / 1000) : ℝ) = ((1000 / 1359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10576_neg : (222362911 / 500000000) ≤ -Real.log (641 / 1000) ∧
    -Real.log (641 / 1000) ≤ (444725823 / 1000000000) := by
  have h := checkLog_sound (w := (359 / 1641)) (n := 12)
    (lo := (222362911 / 500000000)) (hi := (444725823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 641) = 1/(641 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10576 : Bounds (-444725823 / 1000000000) (-222362911 / 500000000) (Real.log (641 / 1000)) := by
  have h := reflection_log_10576_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10577_neg : (71787 / 200000000) ≤ -Real.log (1000000 / 1000359) ∧
    -Real.log (1000000 / 1000359) ≤ (44867 / 125000000) := by
  have h := checkLog_sound (w := (359 / 2000359)) (n := 12)
    (lo := (71787 / 200000000)) (hi := (44867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000359 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000359 / 1000000) = 1/(1000000 / 1000359) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10577 : Bounds (71787 / 200000000) (44867 / 125000000) (Real.log (1000359 / 1000000)) := by
  have h := reflection_log_10577_neg
  have he : Real.log (1000359 / 1000000) = -Real.log (1000000 / 1000359) := by
    rw [show ((1000359 / 1000000) : ℝ) = ((1000000 / 1000359) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10578_neg : (44883 / 125000000) ≤ -Real.log (999641 / 1000000) ∧
    -Real.log (999641 / 1000000) ≤ (71813 / 200000000) := by
  have h := checkLog_sound (w := (359 / 1999641)) (n := 12)
    (lo := (44883 / 125000000)) (hi := (71813 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999641) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999641) = 1/(999641 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10578 : Bounds (-71813 / 200000000) (-44883 / 125000000) (Real.log (999641 / 1000000)) := by
  have h := reflection_log_10578_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10579_neg : (21020011 / 125000000) ≤ -Real.log (500000 / 591563) ∧
    -Real.log (500000 / 591563) ≤ (168160089 / 1000000000) := by
  have h := checkLog_sound (w := (91563 / 1091563)) (n := 12)
    (lo := (21020011 / 125000000)) (hi := (168160089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((591563 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(591563 / 500000) = 1/(500000 / 591563) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10579 : Bounds (21020011 / 125000000) (168160089 / 1000000000) (Real.log (591563 / 500000)) := by
  have h := reflection_log_10579_neg
  have he : Real.log (591563 / 500000) = -Real.log (500000 / 591563) := by
    rw [show ((591563 / 500000) : ℝ) = ((500000 / 591563) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10580_neg : (101135209 / 500000000) ≤ -Real.log (408437 / 500000) ∧
    -Real.log (408437 / 500000) ≤ (202270419 / 1000000000) := by
  have h := checkLog_sound (w := (91563 / 908437)) (n := 12)
    (lo := (101135209 / 500000000)) (hi := (202270419 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 408437) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 408437) = 1/(408437 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10580 : Bounds (-202270419 / 1000000000) (-101135209 / 500000000) (Real.log (408437 / 500000)) := by
  have h := reflection_log_10580_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10581_neg : (4222759 / 25000000) ≤ -Real.log (500000 / 592007) ∧
    -Real.log (500000 / 592007) ≤ (168910361 / 1000000000) := by
  have h := checkLog_sound (w := (92007 / 1092007)) (n := 12)
    (lo := (4222759 / 25000000)) (hi := (168910361 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((592007 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(592007 / 500000) = 1/(500000 / 592007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10581 : Bounds (4222759 / 25000000) (168910361 / 1000000000) (Real.log (592007 / 500000)) := by
  have h := reflection_log_10581_neg
  have he : Real.log (592007 / 500000) = -Real.log (500000 / 592007) := by
    rw [show ((592007 / 500000) : ℝ) = ((500000 / 592007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10582_neg : (203358081 / 1000000000) ≤ -Real.log (407993 / 500000) ∧
    -Real.log (407993 / 500000) ≤ (101679041 / 500000000) := by
  have h := checkLog_sound (w := (92007 / 907993)) (n := 12)
    (lo := (203358081 / 1000000000)) (hi := (101679041 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 407993) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 407993) = 1/(407993 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10582 : Bounds (-101679041 / 500000000) (-203358081 / 1000000000) (Real.log (407993 / 500000)) := by
  have h := reflection_log_10582_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10583_neg : (861193 / 25000000) ≤ -Real.log (241534711951 / 250000000000) ∧
    -Real.log (241534711951 / 250000000000) ≤ (34447721 / 1000000000) := by
  have h := checkLog_sound (w := (8465288049 / 491534711951)) (n := 12)
    (lo := (861193 / 25000000)) (hi := (34447721 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241534711951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241534711951) = 1/(241534711951 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10583 : Bounds (-34447721 / 1000000000) (-861193 / 25000000) (Real.log (241534711951 / 250000000000)) := by
  have h := reflection_log_10583_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10584_neg : (3411033 / 100000000) ≤ -Real.log (241616217031 / 250000000000) ∧
    -Real.log (241616217031 / 250000000000) ≤ (34110331 / 1000000000) := by
  have h := checkLog_sound (w := (8383782969 / 491616217031)) (n := 12)
    (lo := (3411033 / 100000000)) (hi := (34110331 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 241616217031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 241616217031) = 1/(241616217031 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10584 : Bounds (-34110331 / 1000000000) (-3411033 / 100000000) (Real.log (241616217031 / 250000000000)) := by
  have h := reflection_log_10584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10585_neg : (185215253 / 500000000) ≤ -Real.log (10000000000 / 14483580087) ∧
    -Real.log (10000000000 / 14483580087) ≤ (370430507 / 1000000000) := by
  have h := checkLog_sound (w := (4483580087 / 24483580087)) (n := 12)
    (lo := (185215253 / 500000000)) (hi := (370430507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14483580087 / 10000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(14483580087 / 10000000000) = 1/(10000000000 / 14483580087) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10585 : Bounds (185215253 / 500000000) (370430507 / 1000000000) (Real.log (14483580087 / 10000000000)) := by
  have h := reflection_log_10585_neg
  have he : Real.log (14483580087 / 10000000000) = -Real.log (10000000000 / 14483580087) := by
    rw [show ((14483580087 / 10000000000) : ℝ) = ((10000000000 / 14483580087) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10586_neg : (372268441 / 1000000000) ≤ -Real.log (500000000000 / 725511222007) ∧
    -Real.log (500000000000 / 725511222007) ≤ (186134221 / 500000000) := by
  have h := checkLog_sound (w := (225511222007 / 1225511222007)) (n := 12)
    (lo := (372268441 / 1000000000)) (hi := (186134221 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((725511222007 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(725511222007 / 500000000000) = 1/(500000000000 / 725511222007) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10586 : Bounds (372268441 / 1000000000) (186134221 / 500000000) (Real.log (725511222007 / 500000000000)) := by
  have h := reflection_log_10586_neg
  have he : Real.log (725511222007 / 500000000000) = -Real.log (500000000000 / 725511222007) := by
    rw [show ((725511222007 / 500000000000) : ℝ) = ((500000000000 / 725511222007) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10587_neg : (749180003 / 1000000000) ≤ -Real.log (500000000000 / 1057632398753) ∧
    -Real.log (500000000000 / 1057632398753) ≤ (149836001 / 200000000) := by
  have h := checkLog_sound (w := (57632398753 / 2057632398753)) (n := 12)
    (lo := (56032823 / 1000000000)) (hi := (7004103 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1057632398753 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1057632398753 / 1000000000000) = 1/(500000000000 / 1057632398753) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10587 : Bounds (749180003 / 1000000000) (149836001 / 200000000) (Real.log (1057632398753 / 500000000000)) := by
  have h := reflection_log_10587_neg
  have he : Real.log (1057632398753 / 500000000000) = -Real.log (500000000000 / 1057632398753) := by
    rw [show ((1057632398753 / 500000000000) : ℝ) = ((500000000000 / 1057632398753) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10588_neg : (187868739 / 250000000) ≤ -Real.log (500000000000 / 1060062402497) ∧
    -Real.log (500000000000 / 1060062402497) ≤ (375737479 / 500000000) := by
  have h := checkLog_sound (w := (60062402497 / 2060062402497)) (n := 12)
    (lo := (1822743 / 31250000)) (hi := (58327777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1060062402497 / 1000000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1060062402497 / 1000000000000) = 1/(500000000000 / 1060062402497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10588 : Bounds (187868739 / 250000000) (375737479 / 500000000) (Real.log (1060062402497 / 500000000000)) := by
  have h := reflection_log_10588_neg
  have he : Real.log (1060062402497 / 500000000000) = -Real.log (500000000000 / 1060062402497) := by
    rw [show ((1060062402497 / 500000000000) : ℝ) = ((500000000000 / 1060062402497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10589_neg : (307484699 / 1000000000) ≤ -Real.log (25 / 34) ∧
    -Real.log (25 / 34) ≤ (3074847 / 10000000) := by
  have h := checkLog_sound (w := (9 / 59)) (n := 12)
    (lo := (307484699 / 1000000000)) (hi := (3074847 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34 / 25) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34 / 25) = 1/(25 / 34) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10589 : Bounds (307484699 / 1000000000) (3074847 / 10000000) (Real.log (34 / 25)) := by
  have h := reflection_log_10589_neg
  have he : Real.log (34 / 25) = -Real.log (25 / 34) := by
    rw [show ((34 / 25) : ℝ) = ((25 / 34) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10590_neg : (223143551 / 500000000) ≤ -Real.log (16 / 25) ∧
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


theorem reflection_log_10590 : Bounds (-446287103 / 1000000000) (-223143551 / 500000000) (Real.log (16 / 25)) := by
  have h := reflection_log_10590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10591_neg : (71987 / 200000000) ≤ -Real.log (25000 / 25009) ∧
    -Real.log (25000 / 25009) ≤ (703 / 1953125) := by
  have h := checkLog_sound (w := (9 / 50009)) (n := 12)
    (lo := (71987 / 200000000)) (hi := (703 / 1953125))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25009 / 25000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25009 / 25000) = 1/(25000 / 25009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10591 : Bounds (71987 / 200000000) (703 / 1953125) (Real.log (25009 / 25000)) := by
  have h := reflection_log_10591_neg
  have he : Real.log (25009 / 25000) = -Real.log (25000 / 25009) := by
    rw [show ((25009 / 25000) : ℝ) = ((25000 / 25009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10592_neg : (2813 / 7812500) ≤ -Real.log (24991 / 25000) ∧
    -Real.log (24991 / 25000) ≤ (72013 / 200000000) := by
  have h := checkLog_sound (w := (9 / 49991)) (n := 12)
    (lo := (2813 / 7812500)) (hi := (72013 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000 / 24991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000 / 24991) = 1/(24991 / 25000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10592 : Bounds (-72013 / 200000000) (-2813 / 7812500) (Real.log (24991 / 25000)) := by
  have h := reflection_log_10592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10593_neg : (168613867 / 1000000000) ≤ -Real.log (1000000 / 1183663) ∧
    -Real.log (1000000 / 1183663) ≤ (42153467 / 250000000) := by
  have h := checkLog_sound (w := (183663 / 2183663)) (n := 12)
    (lo := (168613867 / 1000000000)) (hi := (42153467 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1183663 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1183663 / 1000000) = 1/(1000000 / 1183663) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10593 : Bounds (168613867 / 1000000000) (42153467 / 250000000) (Real.log (1183663 / 1000000)) := by
  have h := reflection_log_10593_neg
  have he : Real.log (1183663 / 1000000) = -Real.log (1000000 / 1183663) := by
    rw [show ((1183663 / 1000000) : ℝ) = ((1000000 / 1183663) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10594_neg : (202928019 / 1000000000) ≤ -Real.log (816337 / 1000000) ∧
    -Real.log (816337 / 1000000) ≤ (10146401 / 50000000) := by
  have h := checkLog_sound (w := (183663 / 1816337)) (n := 12)
    (lo := (202928019 / 1000000000)) (hi := (10146401 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 816337) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 816337) = 1/(816337 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10594 : Bounds (-10146401 / 50000000) (-202928019 / 1000000000) (Real.log (816337 / 1000000)) := by
  have h := reflection_log_10594_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10595_neg : (42341161 / 250000000) ≤ -Real.log (125000 / 148069) ∧
    -Real.log (125000 / 148069) ≤ (33872929 / 200000000) := by
  have h := checkLog_sound (w := (23069 / 273069)) (n := 12)
    (lo := (42341161 / 250000000)) (hi := (33872929 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((148069 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(148069 / 125000) = 1/(125000 / 148069) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10595 : Bounds (42341161 / 250000000) (33872929 / 200000000) (Real.log (148069 / 125000)) := by
  have h := reflection_log_10595_neg
  have he : Real.log (148069 / 125000) = -Real.log (125000 / 148069) := by
    rw [show ((148069 / 125000) : ℝ) = ((125000 / 148069) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10596_neg : (204017623 / 1000000000) ≤ -Real.log (101931 / 125000) ∧
    -Real.log (101931 / 125000) ≤ (25502203 / 125000000) := by
  have h := checkLog_sound (w := (23069 / 226931)) (n := 12)
    (lo := (204017623 / 1000000000)) (hi := (25502203 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 101931) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 101931) = 1/(101931 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10596 : Bounds (-25502203 / 125000000) (-204017623 / 1000000000) (Real.log (101931 / 125000)) := by
  have h := reflection_log_10596_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10597_neg : (34652979 / 1000000000) ≤ -Real.log (15092821239 / 15625000000) ∧
    -Real.log (15092821239 / 15625000000) ≤ (1732649 / 50000000) := by
  have h := checkLog_sound (w := (532178761 / 30717821239)) (n := 12)
    (lo := (34652979 / 1000000000)) (hi := (1732649 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15092821239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15092821239) = 1/(15092821239 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10597 : Bounds (-1732649 / 50000000) (-34652979 / 1000000000) (Real.log (15092821239 / 15625000000)) := by
  have h := reflection_log_10597_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10598_neg : (34314151 / 1000000000) ≤ -Real.log (966267902431 / 1000000000000) ∧
    -Real.log (966267902431 / 1000000000000) ≤ (4289269 / 125000000) := by
  have h := checkLog_sound (w := (33732097569 / 1966267902431)) (n := 12)
    (lo := (34314151 / 1000000000)) (hi := (4289269 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 966267902431) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 966267902431) = 1/(966267902431 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10598 : Bounds (-4289269 / 125000000) (-34314151 / 1000000000) (Real.log (966267902431 / 1000000000000)) := by
  have h := reflection_log_10598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10599_neg : (185770943 / 500000000) ≤ -Real.log (62500000000 / 90623036197) ∧
    -Real.log (62500000000 / 90623036197) ≤ (371541887 / 1000000000) := by
  have h := checkLog_sound (w := (28123036197 / 153123036197)) (n := 12)
    (lo := (185770943 / 500000000)) (hi := (371541887 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90623036197 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(90623036197 / 62500000000) = 1/(62500000000 / 90623036197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10599 : Bounds (185770943 / 500000000) (371541887 / 1000000000) (Real.log (90623036197 / 62500000000)) := by
  have h := reflection_log_10599_neg
  have he : Real.log (90623036197 / 62500000000) = -Real.log (62500000000 / 90623036197) := by
    rw [show ((90623036197 / 62500000000) : ℝ) = ((62500000000 / 90623036197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10600_neg : (373382267 / 1000000000) ≤ -Real.log (125000000000 / 181579941333) ∧
    -Real.log (125000000000 / 181579941333) ≤ (93345567 / 250000000) := by
  have h := checkLog_sound (w := (56579941333 / 306579941333)) (n := 12)
    (lo := (373382267 / 1000000000)) (hi := (93345567 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((181579941333 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(181579941333 / 125000000000) = 1/(125000000000 / 181579941333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10600 : Bounds (373382267 / 1000000000) (93345567 / 250000000) (Real.log (181579941333 / 125000000000)) := by
  have h := reflection_log_10600_neg
  have he : Real.log (181579941333 / 125000000000) = -Real.log (125000000000 / 181579941333) := by
    rw [show ((181579941333 / 125000000000) : ℝ) = ((125000000000 / 181579941333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10601_neg : (187868739 / 250000000) ≤ -Real.log (7812500000 / 16563475039) ∧
    -Real.log (7812500000 / 16563475039) ≤ (375737479 / 500000000) := by
  have h := checkLog_sound (w := (938475039 / 32188475039)) (n := 12)
    (lo := (1822743 / 31250000)) (hi := (58327777 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((16563475039 / 15625000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(16563475039 / 15625000000) = 1/(7812500000 / 16563475039) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10601 : Bounds (187868739 / 250000000) (375737479 / 500000000) (Real.log (16563475039 / 7812500000)) := by
  have h := reflection_log_10601_neg
  have he : Real.log (16563475039 / 7812500000) = -Real.log (7812500000 / 16563475039) := by
    rw [show ((16563475039 / 7812500000) : ℝ) = ((7812500000 / 16563475039) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10602_neg : (753771801 / 1000000000) ≤ -Real.log (8 / 17) ∧
    -Real.log (8 / 17) ≤ (753771803 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 33)) (n := 12)
    (lo := (60624621 / 1000000000)) (hi := (30312311 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17 / 16) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(17 / 16) = 1/(8 / 17) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10602 : Bounds (753771801 / 1000000000) (753771803 / 1000000000) (Real.log (17 / 8)) := by
  have h := reflection_log_10602_neg
  have he : Real.log (17 / 8) = -Real.log (8 / 17) := by
    rw [show ((17 / 8) : ℝ) = ((8 / 17) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10603_neg : (308219723 / 1000000000) ≤ -Real.log (1000 / 1361) ∧
    -Real.log (1000 / 1361) ≤ (77054931 / 250000000) := by
  have h := checkLog_sound (w := (361 / 2361)) (n := 12)
    (lo := (308219723 / 1000000000)) (hi := (77054931 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1361 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1361 / 1000) = 1/(1000 / 1361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10603 : Bounds (308219723 / 1000000000) (77054931 / 250000000) (Real.log (1361 / 1000)) := by
  have h := reflection_log_10603_neg
  have he : Real.log (1361 / 1000) = -Real.log (1000 / 1361) := by
    rw [show ((1361 / 1000) : ℝ) = ((1000 / 1361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10604_neg : (55981353 / 125000000) ≤ -Real.log (639 / 1000) ∧
    -Real.log (639 / 1000) ≤ (17914033 / 40000000) := by
  have h := checkLog_sound (w := (361 / 1639)) (n := 12)
    (lo := (55981353 / 125000000)) (hi := (17914033 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 639) = 1/(639 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10604 : Bounds (-17914033 / 40000000) (-55981353 / 125000000) (Real.log (639 / 1000)) := by
  have h := reflection_log_10604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10605_neg : (180467 / 500000000) ≤ -Real.log (1000000 / 1000361) ∧
    -Real.log (1000000 / 1000361) ≤ (72187 / 200000000) := by
  have h := checkLog_sound (w := (361 / 2000361)) (n := 12)
    (lo := (180467 / 500000000)) (hi := (72187 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000361 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000361 / 1000000) = 1/(1000000 / 1000361) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10605 : Bounds (180467 / 500000000) (72187 / 200000000) (Real.log (1000361 / 1000000)) := by
  have h := reflection_log_10605_neg
  have he : Real.log (1000361 / 1000000) = -Real.log (1000000 / 1000361) := by
    rw [show ((1000361 / 1000000) : ℝ) = ((1000000 / 1000361) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10606_neg : (72213 / 200000000) ≤ -Real.log (999639 / 1000000) ∧
    -Real.log (999639 / 1000000) ≤ (180533 / 500000000) := by
  have h := checkLog_sound (w := (361 / 1999639)) (n := 12)
    (lo := (72213 / 200000000)) (hi := (180533 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999639) = 1/(999639 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10606 : Bounds (-180533 / 500000000) (-72213 / 200000000) (Real.log (999639 / 1000000)) := by
  have h := reflection_log_10606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10607_neg : (169818721 / 1000000000) ≤ -Real.log (100000 / 118509) ∧
    -Real.log (100000 / 118509) ≤ (84909361 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 218509)) (n := 12)
    (lo := (169818721 / 1000000000)) (hi := (84909361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((118509 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(118509 / 100000) = 1/(100000 / 118509) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10607 : Bounds (169818721 / 1000000000) (84909361 / 500000000) (Real.log (118509 / 100000)) := by
  have h := reflection_log_10607_neg
  have he : Real.log (118509 / 100000) = -Real.log (100000 / 118509) := by
    rw [show ((118509 / 100000) : ℝ) = ((100000 / 118509) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10608_neg : (204677601 / 1000000000) ≤ -Real.log (81491 / 100000) ∧
    -Real.log (81491 / 100000) ≤ (102338801 / 500000000) := by
  have h := checkLog_sound (w := (18509 / 181491)) (n := 12)
    (lo := (204677601 / 1000000000)) (hi := (102338801 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 81491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 81491) = 1/(81491 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10608 : Bounds (-102338801 / 500000000) (-204677601 / 1000000000) (Real.log (81491 / 100000)) := by
  have h := reflection_log_10608_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10609_neg : (54467 / 1562500) ≤ -Real.log (9657416919 / 10000000000) ∧
    -Real.log (9657416919 / 10000000000) ≤ (34858881 / 1000000000) := by
  have h := checkLog_sound (w := (342583081 / 19657416919)) (n := 12)
    (lo := (54467 / 1562500)) (hi := (34858881 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 9657416919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 9657416919) = 1/(9657416919 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10609 : Bounds (-34858881 / 1000000000) (-54467 / 1562500) (Real.log (9657416919 / 10000000000)) := by
  have h := reflection_log_10609_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10610_neg : (3451861 / 100000000) ≤ -Real.log (24151759 / 25000000) ∧
    -Real.log (24151759 / 25000000) ≤ (34518611 / 1000000000) := by
  have h := checkLog_sound (w := (848241 / 49151759)) (n := 12)
    (lo := (3451861 / 100000000)) (hi := (34518611 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25000000 / 24151759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(25000000 / 24151759) = 1/(24151759 / 25000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10610 : Bounds (-34518611 / 1000000000) (-3451861 / 100000000) (Real.log (24151759 / 25000000)) := by
  have h := reflection_log_10610_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10611_neg : (187248161 / 500000000) ≤ -Real.log (500000000000 / 727129376251) ∧
    -Real.log (500000000000 / 727129376251) ≤ (374496323 / 1000000000) := by
  have h := checkLog_sound (w := (227129376251 / 1227129376251)) (n := 12)
    (lo := (187248161 / 500000000)) (hi := (374496323 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((727129376251 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(727129376251 / 500000000000) = 1/(500000000000 / 727129376251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10611 : Bounds (187248161 / 500000000) (374496323 / 1000000000) (Real.log (727129376251 / 500000000000)) := by
  have h := reflection_log_10611_neg
  have he : Real.log (727129376251 / 500000000000) = -Real.log (500000000000 / 727129376251) := by
    rw [show ((727129376251 / 500000000000) : ℝ) = ((500000000000 / 727129376251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10612_neg : (756070547 / 1000000000) ≤ -Real.log (250000000000 / 532472613459) ∧
    -Real.log (250000000000 / 532472613459) ≤ (756070549 / 1000000000) := by
  have h := checkLog_sound (w := (32472613459 / 1032472613459)) (n := 12)
    (lo := (62923367 / 1000000000)) (hi := (7865421 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((532472613459 / 500000000000) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(532472613459 / 500000000000) = 1/(250000000000 / 532472613459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10612 : Bounds (756070547 / 1000000000) (756070549 / 1000000000) (Real.log (532472613459 / 250000000000)) := by
  have h := reflection_log_10612_neg
  have he : Real.log (532472613459 / 250000000000) = -Real.log (250000000000 / 532472613459) := by
    rw [show ((532472613459 / 250000000000) : ℝ) = ((250000000000 / 532472613459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10613_neg : (308954207 / 1000000000) ≤ -Real.log (500 / 681) ∧
    -Real.log (500 / 681) ≤ (9654819 / 31250000) := by
  have h := checkLog_sound (w := (181 / 1181)) (n := 12)
    (lo := (308954207 / 1000000000)) (hi := (9654819 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((681 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(681 / 500) = 1/(500 / 681) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10613 : Bounds (308954207 / 1000000000) (9654819 / 31250000) (Real.log (681 / 500)) := by
  have h := reflection_log_10613_neg
  have he : Real.log (681 / 500) = -Real.log (500 / 681) := by
    rw [show ((681 / 500) : ℝ) = ((500 / 681) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10614_neg : (89883399 / 200000000) ≤ -Real.log (319 / 500) ∧
    -Real.log (319 / 500) ≤ (112354249 / 250000000) := by
  have h := checkLog_sound (w := (181 / 819)) (n := 12)
    (lo := (89883399 / 200000000)) (hi := (112354249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 319) = 1/(319 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10614 : Bounds (-112354249 / 250000000) (-89883399 / 200000000) (Real.log (319 / 500)) := by
  have h := reflection_log_10614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10615_neg : (180967 / 500000000) ≤ -Real.log (500000 / 500181) ∧
    -Real.log (500000 / 500181) ≤ (72387 / 200000000) := by
  have h := checkLog_sound (w := (181 / 1000181)) (n := 12)
    (lo := (180967 / 500000000)) (hi := (72387 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500181 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500181 / 500000) = 1/(500000 / 500181) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10615 : Bounds (180967 / 500000000) (72387 / 200000000) (Real.log (500181 / 500000)) := by
  have h := reflection_log_10615_neg
  have he : Real.log (500181 / 500000) = -Real.log (500000 / 500181) := by
    rw [show ((500181 / 500000) : ℝ) = ((500000 / 500181) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10616_neg : (72413 / 200000000) ≤ -Real.log (499819 / 500000) ∧
    -Real.log (499819 / 500000) ≤ (181033 / 500000000) := by
  have h := checkLog_sound (w := (181 / 999819)) (n := 12)
    (lo := (72413 / 200000000)) (hi := (181033 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499819) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499819) = 1/(499819 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10616 : Bounds (-181033 / 500000000) (-72413 / 200000000) (Real.log (499819 / 500000)) := by
  have h := reflection_log_10616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10617_neg : (169520809 / 1000000000) ≤ -Real.log (1000000 / 1184737) ∧
    -Real.log (1000000 / 1184737) ≤ (16952081 / 100000000) := by
  have h := checkLog_sound (w := (184737 / 2184737)) (n := 12)
    (lo := (169520809 / 1000000000)) (hi := (16952081 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1184737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1184737 / 1000000) = 1/(1000000 / 1184737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10617 : Bounds (169520809 / 1000000000) (16952081 / 100000000) (Real.log (1184737 / 1000000)) := by
  have h := reflection_log_10617_neg
  have he : Real.log (1184737 / 1000000) = -Real.log (1000000 / 1184737) := by
    rw [show ((1184737 / 1000000) : ℝ) = ((1000000 / 1184737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10618_neg : (102122259 / 500000000) ≤ -Real.log (815263 / 1000000) ∧
    -Real.log (815263 / 1000000) ≤ (204244519 / 1000000000) := by
  have h := checkLog_sound (w := (184737 / 1815263)) (n := 12)
    (lo := (102122259 / 500000000)) (hi := (204244519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 815263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 815263) = 1/(815263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10618 : Bounds (-204244519 / 1000000000) (-102122259 / 500000000) (Real.log (815263 / 1000000)) := by
  have h := reflection_log_10618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10619_neg : (10642037 / 62500000) ≤ -Real.log (250000 / 296407) ∧
    -Real.log (250000 / 296407) ≤ (170272593 / 1000000000) := by
  have h := checkLog_sound (w := (46407 / 546407)) (n := 12)
    (lo := (10642037 / 62500000)) (hi := (170272593 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((296407 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(296407 / 250000) = 1/(250000 / 296407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10619 : Bounds (10642037 / 62500000) (170272593 / 1000000000) (Real.log (296407 / 250000)) := by
  have h := reflection_log_10619_neg
  have he : Real.log (296407 / 250000) = -Real.log (250000 / 296407) := by
    rw [show ((296407 / 250000) : ℝ) = ((250000 / 296407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_10620_neg : (102669007 / 500000000) ≤ -Real.log (203593 / 250000) ∧
    -Real.log (203593 / 250000) ≤ (41067603 / 200000000) := by
  have h := checkLog_sound (w := (46407 / 453593)) (n := 12)
    (lo := (102669007 / 500000000)) (hi := (41067603 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 203593) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 203593) = 1/(203593 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10620 : Bounds (-41067603 / 200000000) (-102669007 / 500000000) (Real.log (203593 / 250000)) := by
  have h := reflection_log_10620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10621_neg : (17532711 / 500000000) ≤ -Real.log (60346390351 / 62500000000) ∧
    -Real.log (60346390351 / 62500000000) ≤ (35065423 / 1000000000) := by
  have h := checkLog_sound (w := (2153609649 / 122846390351)) (n := 12)
    (lo := (17532711 / 500000000)) (hi := (35065423 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 60346390351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 60346390351) = 1/(60346390351 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10621 : Bounds (-35065423 / 1000000000) (-17532711 / 500000000) (Real.log (60346390351 / 62500000000)) := by
  have h := reflection_log_10621_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10622_neg : (34723709 / 1000000000) ≤ -Real.log (965872240831 / 1000000000000) ∧
    -Real.log (965872240831 / 1000000000000) ≤ (3472371 / 100000000) := by
  have h := checkLog_sound (w := (34127759169 / 1965872240831)) (n := 12)
    (lo := (34723709 / 1000000000)) (hi := (3472371 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 965872240831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 965872240831) = 1/(965872240831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10622 : Bounds (-3472371 / 100000000) (-34723709 / 1000000000) (Real.log (965872240831 / 1000000000000)) := by
  have h := reflection_log_10622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_10623_neg : (373765327 / 1000000000) ≤ -Real.log (250000000000 / 363299021297) ∧
    -Real.log (250000000000 / 363299021297) ≤ (23360333 / 62500000) := by
  have h := checkLog_sound (w := (113299021297 / 613299021297)) (n := 12)
    (lo := (373765327 / 1000000000)) (hi := (23360333 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((363299021297 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(363299021297 / 250000000000) = 1/(250000000000 / 363299021297) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_10623 : Bounds (373765327 / 1000000000) (23360333 / 62500000) (Real.log (363299021297 / 250000000000)) := by
  have h := reflection_log_10623_neg
  have he : Real.log (363299021297 / 250000000000) = -Real.log (250000000000 / 363299021297) := by
    rw [show ((363299021297 / 250000000000) : ℝ) = ((250000000000 / 363299021297) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


