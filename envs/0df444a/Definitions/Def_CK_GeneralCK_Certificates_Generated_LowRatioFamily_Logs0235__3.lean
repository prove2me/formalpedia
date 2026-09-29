-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0235__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0235__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:48:08.09385+00:00
-- url     : https://prove2.me/theorems/1db569d9-9e3f-4b68-9353-df3cf6827798
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0235 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0236, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0235 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0236, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0237)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0235 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0236, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0237)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0235 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0236, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0237) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0235 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0236, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0237).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0235 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15040_neg : (490804111 / 500000000) ≤ -Real.log (93677 / 250000) ∧
    -Real.log (93677 / 250000) ≤ (30675257 / 31250000) := by
  have h := checkLog_sound (w := (31323 / 218677)) (n := 12)
    (lo := (144230521 / 500000000)) (hi := (288461043 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 93677) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 93677) = 1/(93677 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15040 : Bounds (-30675257 / 31250000) (-490804111 / 500000000) (Real.log (93677 / 250000)) := by
  have h := reflection_log_15040_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15041_neg : (243437133 / 500000000) ≤ -Real.log (500000 / 813611) ∧
    -Real.log (500000 / 813611) ≤ (486874267 / 1000000000) := by
  have h := checkLog_sound (w := (313611 / 1313611)) (n := 12)
    (lo := (243437133 / 500000000)) (hi := (486874267 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813611 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813611 / 500000) = 1/(500000 / 813611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15041 : Bounds (243437133 / 500000000) (486874267 / 1000000000) (Real.log (813611 / 500000)) := by
  have h := reflection_log_15041_neg
  have he : Real.log (813611 / 500000) = -Real.log (500000 / 813611) := by
    rw [show ((813611 / 500000) : ℝ) = ((500000 / 813611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15042_neg : (98677221 / 100000000) ≤ -Real.log (186389 / 500000) ∧
    -Real.log (186389 / 500000) ≤ (246693053 / 250000000) := by
  have h := checkLog_sound (w := (63611 / 436389)) (n := 12)
    (lo := (29362503 / 100000000)) (hi := (293625031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186389) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 186389) = 1/(186389 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15042 : Bounds (-246693053 / 250000000) (-98677221 / 100000000) (Real.log (186389 / 500000)) := by
  have h := reflection_log_15042_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15043_neg : (62487243 / 125000000) ≤ -Real.log (151648140679 / 250000000000) ∧
    -Real.log (151648140679 / 250000000000) ≤ (99979589 / 200000000) := by
  have h := checkLog_sound (w := (98351859321 / 401648140679)) (n := 12)
    (lo := (62487243 / 125000000)) (hi := (99979589 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151648140679) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151648140679) = 1/(151648140679 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15043 : Bounds (-99979589 / 200000000) (-62487243 / 125000000) (Real.log (151648140679 / 250000000000)) := by
  have h := reflection_log_15043_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15044_neg : (495920731 / 1000000000) ≤ -Real.log (38063119671 / 62500000000) ∧
    -Real.log (38063119671 / 62500000000) ≤ (123980183 / 250000000) := by
  have h := checkLog_sound (w := (24436880329 / 100563119671)) (n := 12)
    (lo := (495920731 / 1000000000)) (hi := (123980183 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 38063119671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 38063119671) = 1/(38063119671 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15044 : Bounds (-123980183 / 250000000) (-495920731 / 1000000000) (Real.log (38063119671 / 62500000000)) := by
  have h := reflection_log_15044_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15045_neg : (1467295713 / 1000000000) ≤ -Real.log (500000000000 / 2168744729229) ∧
    -Real.log (500000000000 / 2168744729229) ≤ (366823929 / 250000000) := by
  have h := checkLog_sound (w := (168744729229 / 4168744729229)) (n := 12)
    (lo := (81001353 / 1000000000)) (hi := (40500677 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2168744729229 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2168744729229 / 2000000000000) = 1/(500000000000 / 2168744729229) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15045 : Bounds (1467295713 / 1000000000) (366823929 / 250000000) (Real.log (2168744729229 / 500000000000)) := by
  have h := reflection_log_15045_neg
  have he : Real.log (2168744729229 / 500000000000) = -Real.log (500000000000 / 2168744729229) := by
    rw [show ((2168744729229 / 500000000000) : ℝ) = ((500000000000 / 2168744729229) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15046_neg : (368411619 / 250000000) ≤ -Real.log (500000000000 / 2182561739159) ∧
    -Real.log (500000000000 / 2182561739159) ≤ (1473646479 / 1000000000) := by
  have h := checkLog_sound (w := (182561739159 / 4182561739159)) (n := 12)
    (lo := (21838029 / 250000000)) (hi := (87352117 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2182561739159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2182561739159 / 2000000000000) = 1/(500000000000 / 2182561739159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15046 : Bounds (368411619 / 250000000) (1473646479 / 1000000000) (Real.log (2182561739159 / 500000000000)) := by
  have h := reflection_log_15046_neg
  have he : Real.log (2182561739159 / 500000000000) = -Real.log (500000000000 / 2182561739159) := by
    rw [show ((2182561739159 / 500000000000) : ℝ) = ((500000000000 / 2182561739159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15047_neg : (899759811 / 200000000) ≤ -Real.log (100000000000 / 8990909090909) ∧
    -Real.log (100000000000 / 8990909090909) ≤ (2249399531 / 500000000) := by
  have h := checkLog_sound (w := (2590909090909 / 15390909090909)) (n := 12)
    (lo := (13596639 / 40000000)) (hi := (42489497 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((8990909090909 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(8990909090909 / 6400000000000) = 1/(100000000000 / 8990909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15047 : Bounds (899759811 / 200000000) (2249399531 / 500000000) (Real.log (8990909090909 / 100000000000)) := by
  have h := reflection_log_15047_neg
  have he : Real.log (8990909090909 / 100000000000) = -Real.log (100000000000 / 8990909090909) := by
    rw [show ((8990909090909 / 100000000000) : ℝ) = ((100000000000 / 8990909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15048_neg : (568228063 / 125000000) ≤ -Real.log (62500000000 / 5889880952381) ∧
    -Real.log (62500000000 / 5889880952381) ≤ (4545824511 / 1000000000) := by
  have h := checkLog_sound (w := (1889880952381 / 9889880952381)) (n := 12)
    (lo := (24183839 / 62500000)) (hi := (15477657 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5889880952381 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(5889880952381 / 4000000000000) = 1/(62500000000 / 5889880952381) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15048 : Bounds (568228063 / 125000000) (4545824511 / 1000000000) (Real.log (5889880952381 / 62500000000)) := by
  have h := reflection_log_15048_neg
  have he : Real.log (5889880952381 / 62500000000) = -Real.log (62500000000 / 5889880952381) := by
    rw [show ((5889880952381 / 62500000000) : ℝ) = ((62500000000 / 5889880952381) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15049_neg : (170774211 / 250000000) ≤ -Real.log (50 / 99) ∧
    -Real.log (50 / 99) ≤ (136619369 / 200000000) := by
  have h := checkLog_sound (w := (49 / 149)) (n := 12)
    (lo := (170774211 / 250000000)) (hi := (136619369 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 50) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(99 / 50) = 1/(50 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15049 : Bounds (170774211 / 250000000) (136619369 / 200000000) (Real.log (99 / 50)) := by
  have h := reflection_log_15049_neg
  have he : Real.log (99 / 50) = -Real.log (50 / 99) := by
    rw [show ((99 / 50) : ℝ) = ((50 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15050_neg : (1956011501 / 500000000) ≤ -Real.log (1 / 50) ∧
    -Real.log (1 / 50) ≤ (122250719 / 31250000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(25 / 16) = 1/(1 / 50) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15050 : Bounds (-122250719 / 31250000) (-1956011501 / 500000000) (Real.log (1 / 50)) := by
  have h := reflection_log_15050_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15051_neg : (3061 / 3125000) ≤ -Real.log (50000 / 50049) ∧
    -Real.log (50000 / 50049) ≤ (979521 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 100049)) (n := 12)
    (lo := (3061 / 3125000)) (hi := (979521 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50049 / 50000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50049 / 50000) = 1/(50000 / 50049) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15051 : Bounds (3061 / 3125000) (979521 / 1000000000) (Real.log (50049 / 50000)) := by
  have h := reflection_log_15051_neg
  have he : Real.log (50049 / 50000) = -Real.log (50000 / 50049) := by
    rw [show ((50049 / 50000) : ℝ) = ((50000 / 50049) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15052_neg : (383 / 390625) ≤ -Real.log (49951 / 50000) ∧
    -Real.log (49951 / 50000) ≤ (980481 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 99951)) (n := 12)
    (lo := (383 / 390625)) (hi := (980481 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 49951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(50000 / 49951) = 1/(49951 / 50000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15052 : Bounds (-980481 / 1000000000) (-383 / 390625) (Real.log (49951 / 50000)) := by
  have h := reflection_log_15052_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15053_neg : (97296053 / 200000000) ≤ -Real.log (1000000 / 1626581) ∧
    -Real.log (1000000 / 1626581) ≤ (243240133 / 500000000) := by
  have h := checkLog_sound (w := (626581 / 2626581)) (n := 12)
    (lo := (97296053 / 200000000)) (hi := (243240133 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1626581 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1626581 / 1000000) = 1/(1000000 / 1626581) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15053 : Bounds (97296053 / 200000000) (243240133 / 500000000) (Real.log (1626581 / 1000000)) := by
  have h := reflection_log_15053_neg
  have he : Real.log (1626581 / 1000000) = -Real.log (1000000 / 1626581) := by
    rw [show ((1626581 / 1000000) : ℝ) = ((1000000 / 1626581) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15054_neg : (246263541 / 250000000) ≤ -Real.log (373419 / 1000000) ∧
    -Real.log (373419 / 1000000) ≤ (492527083 / 500000000) := by
  have h := checkLog_sound (w := (126581 / 873419)) (n := 12)
    (lo := (36488373 / 125000000)) (hi := (58381397 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 373419) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 373419) = 1/(373419 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15054 : Bounds (-492527083 / 500000000) (-246263541 / 250000000) (Real.log (373419 / 1000000)) := by
  have h := reflection_log_15054_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15055_neg : (97534571 / 200000000) ≤ -Real.log (500000 / 814261) ∧
    -Real.log (500000 / 814261) ≤ (60959107 / 125000000) := by
  have h := checkLog_sound (w := (314261 / 1314261)) (n := 12)
    (lo := (97534571 / 200000000)) (hi := (60959107 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814261 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814261 / 500000) = 1/(500000 / 814261) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15055 : Bounds (97534571 / 200000000) (60959107 / 125000000) (Real.log (814261 / 500000)) := by
  have h := reflection_log_15055_neg
  have he : Real.log (814261 / 500000) = -Real.log (500000 / 814261) := by
    rw [show ((814261 / 500000) : ℝ) = ((500000 / 814261) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15056_neg : (198053127 / 200000000) ≤ -Real.log (185739 / 500000) ∧
    -Real.log (185739 / 500000) ≤ (990265637 / 1000000000) := by
  have h := checkLog_sound (w := (64261 / 435739)) (n := 12)
    (lo := (59423691 / 200000000)) (hi := (37139807 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185739) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185739) = 1/(185739 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15056 : Bounds (-990265637 / 1000000000) (-198053127 / 200000000) (Real.log (185739 / 500000)) := by
  have h := reflection_log_15056_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15057_neg : (25129639 / 50000000) ≤ -Real.log (151240023879 / 250000000000) ∧
    -Real.log (151240023879 / 250000000000) ≤ (502592781 / 1000000000) := by
  have h := checkLog_sound (w := (98759976121 / 401240023879)) (n := 12)
    (lo := (25129639 / 50000000)) (hi := (502592781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151240023879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151240023879) = 1/(151240023879 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15057 : Bounds (-502592781 / 1000000000) (-25129639 / 50000000) (Real.log (151240023879 / 250000000000)) := by
  have h := reflection_log_15057_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15058_neg : (498573899 / 1000000000) ≤ -Real.log (607396250439 / 1000000000000) ∧
    -Real.log (607396250439 / 1000000000000) ≤ (4985739 / 10000000) := by
  have h := checkLog_sound (w := (392603749561 / 1607396250439)) (n := 12)
    (lo := (498573899 / 1000000000)) (hi := (4985739 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 607396250439) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 607396250439) = 1/(607396250439 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15058 : Bounds (-4985739 / 10000000) (-498573899 / 1000000000) (Real.log (607396250439 / 1000000000000)) := by
  have h := reflection_log_15058_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15059_neg : (147153443 / 100000000) ≤ -Real.log (62500000000 / 272244616637) ∧
    -Real.log (62500000000 / 272244616637) ≤ (1471534433 / 1000000000) := by
  have h := checkLog_sound (w := (22244616637 / 522244616637)) (n := 12)
    (lo := (8524007 / 100000000)) (hi := (85240071 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((272244616637 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(272244616637 / 250000000000) = 1/(62500000000 / 272244616637) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15059 : Bounds (147153443 / 100000000) (1471534433 / 1000000000) (Real.log (272244616637 / 62500000000)) := by
  have h := reflection_log_15059_neg
  have he : Real.log (272244616637 / 62500000000) = -Real.log (62500000000 / 272244616637) := by
    rw [show ((272244616637 / 62500000000) : ℝ) = ((62500000000 / 272244616637) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15060_neg : (1477938489 / 1000000000) ≤ -Real.log (250000000000 / 1095974727979) ∧
    -Real.log (250000000000 / 1095974727979) ≤ (369484623 / 250000000) := by
  have h := checkLog_sound (w := (95974727979 / 2095974727979)) (n := 12)
    (lo := (91644129 / 1000000000)) (hi := (9164413 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1095974727979 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1095974727979 / 1000000000000) = 1/(250000000000 / 1095974727979) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15060 : Bounds (1477938489 / 1000000000) (369484623 / 250000000) (Real.log (1095974727979 / 250000000000)) := by
  have h := reflection_log_15060_neg
  have he : Real.log (1095974727979 / 250000000000) = -Real.log (250000000000 / 1095974727979) := by
    rw [show ((1095974727979 / 250000000000) : ℝ) = ((250000000000 / 1095974727979) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15061_neg : (568228063 / 125000000) ≤ -Real.log (500000000000 / 47119047619047) ∧
    -Real.log (500000000000 / 47119047619047) ≤ (4545824511 / 1000000000) := by
  have h := checkLog_sound (w := (15119047619047 / 79119047619047)) (n := 12)
    (lo := (24183839 / 62500000)) (hi := (15477657 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((47119047619047 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(47119047619047 / 32000000000000) = 1/(500000000000 / 47119047619047) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15061 : Bounds (568228063 / 125000000) (4545824511 / 1000000000) (Real.log (47119047619047 / 500000000000)) := by
  have h := reflection_log_15061_neg
  have he : Real.log (47119047619047 / 500000000000) = -Real.log (500000000000 / 47119047619047) := by
    rw [show ((47119047619047 / 500000000000) : ℝ) = ((500000000000 / 47119047619047) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15062_neg : (2297559923 / 500000000) ≤ -Real.log (1 / 99) ∧
    -Real.log (1 / 99) ≤ (4595119853 / 1000000000) := by
  have h := checkLog_sound (w := (35 / 163)) (n := 12)
    (lo := (218118383 / 500000000)) (hi := (436236767 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((99 / 64) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(99 / 64) = 1/(1 / 99) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15062 : Bounds (2297559923 / 500000000) (4595119853 / 1000000000) (Real.log (99 / 1)) := by
  have h := reflection_log_15062_neg
  have he : Real.log (99 / 1) = -Real.log (1 / 99) := by
    rw [show ((99 / 1) : ℝ) = ((1 / 99) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15063_neg : (683601767 / 1000000000) ≤ -Real.log (1000 / 1981) ∧
    -Real.log (1000 / 1981) ≤ (85450221 / 125000000) := by
  have h := checkLog_sound (w := (981 / 2981)) (n := 12)
    (lo := (683601767 / 1000000000)) (hi := (85450221 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1981 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1981 / 1000) = 1/(1000 / 1981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15063 : Bounds (683601767 / 1000000000) (85450221 / 125000000) (Real.log (1981 / 1000)) := by
  have h := reflection_log_15063_neg
  have he : Real.log (1981 / 1000) = -Real.log (1000 / 1981) := by
    rw [show ((1981 / 1000) : ℝ) = ((1000 / 1981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15064_neg : (3963316297 / 1000000000) ≤ -Real.log (19 / 1000) ∧
    -Real.log (19 / 1000) ≤ (3963316303 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 201)) (n := 12)
    (lo := (497580397 / 1000000000)) (hi := (248790199 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 76) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 76) = 1/(19 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15064 : Bounds (-3963316303 / 1000000000) (-3963316297 / 1000000000) (Real.log (19 / 1000)) := by
  have h := reflection_log_15064_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15065_neg : (980519 / 1000000000) ≤ -Real.log (1000000 / 1000981) ∧
    -Real.log (1000000 / 1000981) ≤ (24513 / 25000000) := by
  have h := checkLog_sound (w := (981 / 2000981)) (n := 12)
    (lo := (980519 / 1000000000)) (hi := (24513 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000981 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000981 / 1000000) = 1/(1000000 / 1000981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15065 : Bounds (980519 / 1000000000) (24513 / 25000000) (Real.log (1000981 / 1000000)) := by
  have h := reflection_log_15065_neg
  have he : Real.log (1000981 / 1000000) = -Real.log (1000000 / 1000981) := by
    rw [show ((1000981 / 1000000) : ℝ) = ((1000000 / 1000981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15066_neg : (981481 / 1000000000) ≤ -Real.log (999019 / 1000000) ∧
    -Real.log (999019 / 1000000) ≤ (490741 / 500000000) := by
  have h := checkLog_sound (w := (981 / 1999019)) (n := 12)
    (lo := (981481 / 1000000000)) (hi := (490741 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999019) = 1/(999019 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15066 : Bounds (-490741 / 500000000) (-981481 / 1000000000) (Real.log (999019 / 1000000)) := by
  have h := reflection_log_15066_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15067_neg : (487279783 / 1000000000) ≤ -Real.log (500000 / 813941) ∧
    -Real.log (500000 / 813941) ≤ (60909973 / 125000000) := by
  have h := checkLog_sound (w := (313941 / 1313941)) (n := 12)
    (lo := (487279783 / 1000000000)) (hi := (60909973 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((813941 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(813941 / 500000) = 1/(500000 / 813941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15067 : Bounds (487279783 / 1000000000) (60909973 / 125000000) (Real.log (813941 / 500000)) := by
  have h := reflection_log_15067_neg
  have he : Real.log (813941 / 500000) = -Real.log (500000 / 813941) := by
    rw [show ((813941 / 500000) : ℝ) = ((500000 / 813941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15068_neg : (98854427 / 100000000) ≤ -Real.log (186059 / 500000) ∧
    -Real.log (186059 / 500000) ≤ (61784017 / 62500000) := by
  have h := checkLog_sound (w := (63941 / 436059)) (n := 12)
    (lo := (29539709 / 100000000)) (hi := (295397091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 186059) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 186059) = 1/(186059 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15068 : Bounds (-61784017 / 62500000) (-98854427 / 100000000) (Real.log (186059 / 500000)) := by
  have h := reflection_log_15068_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15069_neg : (488478169 / 1000000000) ≤ -Real.log (500000 / 814917) ∧
    -Real.log (500000 / 814917) ≤ (48847817 / 100000000) := by
  have h := checkLog_sound (w := (314917 / 1314917)) (n := 12)
    (lo := (488478169 / 1000000000)) (hi := (48847817 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814917 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814917 / 500000) = 1/(500000 / 814917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15069 : Bounds (488478169 / 1000000000) (48847817 / 100000000) (Real.log (814917 / 500000)) := by
  have h := reflection_log_15069_neg
  have he : Real.log (814917 / 500000) = -Real.log (500000 / 814917) := by
    rw [show ((814917 / 500000) : ℝ) = ((500000 / 814917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15070_neg : (248450931 / 250000000) ≤ -Real.log (185083 / 500000) ∧
    -Real.log (185083 / 500000) ≤ (496901863 / 500000000) := by
  have h := checkLog_sound (w := (64917 / 435083)) (n := 12)
    (lo := (9395517 / 31250000)) (hi := (60131309 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185083) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185083) = 1/(185083 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15070 : Bounds (-496901863 / 500000000) (-248450931 / 250000000) (Real.log (185083 / 500000)) := by
  have h := reflection_log_15070_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15071_neg : (126331389 / 250000000) ≤ -Real.log (150827283111 / 250000000000) ∧
    -Real.log (150827283111 / 250000000000) ≤ (505325557 / 1000000000) := by
  have h := checkLog_sound (w := (99172716889 / 400827283111)) (n := 12)
    (lo := (126331389 / 250000000)) (hi := (505325557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 150827283111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 150827283111) = 1/(150827283111 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15071 : Bounds (-505325557 / 1000000000) (-126331389 / 250000000) (Real.log (150827283111 / 250000000000)) := by
  have h := reflection_log_15071_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15072_neg : (501264487 / 1000000000) ≤ -Real.log (151441048519 / 250000000000) ∧
    -Real.log (151441048519 / 250000000000) ≤ (62658061 / 125000000) := by
  have h := checkLog_sound (w := (98558951481 / 401441048519)) (n := 12)
    (lo := (501264487 / 1000000000)) (hi := (62658061 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151441048519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151441048519) = 1/(151441048519 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15072 : Bounds (-62658061 / 125000000) (-501264487 / 1000000000) (Real.log (151441048519 / 250000000000)) := by
  have h := reflection_log_15072_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15073_neg : (368956013 / 250000000) ≤ -Real.log (50000000000 / 218731961367) ∧
    -Real.log (50000000000 / 218731961367) ≤ (295164811 / 200000000) := by
  have h := checkLog_sound (w := (18731961367 / 418731961367)) (n := 12)
    (lo := (22382423 / 250000000)) (hi := (89529693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((218731961367 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(218731961367 / 200000000000) = 1/(50000000000 / 218731961367) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15073 : Bounds (368956013 / 250000000) (295164811 / 200000000) (Real.log (218731961367 / 50000000000)) := by
  have h := reflection_log_15073_neg
  have he : Real.log (218731961367 / 50000000000) = -Real.log (50000000000 / 218731961367) := by
    rw [show ((218731961367 / 50000000000) : ℝ) = ((50000000000 / 218731961367) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15074_neg : (1482281893 / 1000000000) ≤ -Real.log (500000000000 / 2201490682559) ∧
    -Real.log (500000000000 / 2201490682559) ≤ (185285237 / 125000000) := by
  have h := checkLog_sound (w := (201490682559 / 4201490682559)) (n := 12)
    (lo := (95987533 / 1000000000)) (hi := (47993767 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2201490682559 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2201490682559 / 2000000000000) = 1/(500000000000 / 2201490682559) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15074 : Bounds (1482281893 / 1000000000) (185285237 / 125000000) (Real.log (2201490682559 / 500000000000)) := by
  have h := reflection_log_15074_neg
  have he : Real.log (2201490682559 / 500000000000) = -Real.log (500000000000 / 2201490682559) := by
    rw [show ((2201490682559 / 500000000000) : ℝ) = ((500000000000 / 2201490682559) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15075_neg : (290432379 / 62500000) ≤ -Real.log (500000000000 / 52131578947369) ∧
    -Real.log (500000000000 / 52131578947369) ≤ (4646918071 / 1000000000) := by
  have h := checkLog_sound (w := (20131578947369 / 84131578947369)) (n := 12)
    (lo := (61004373 / 125000000)) (hi := (97606997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((52131578947369 / 32000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(52131578947369 / 32000000000000) = 1/(500000000000 / 52131578947369) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15075 : Bounds (290432379 / 62500000) (4646918071 / 1000000000) (Real.log (52131578947369 / 500000000000)) := by
  have h := reflection_log_15075_neg
  have he : Real.log (52131578947369 / 500000000000) = -Real.log (500000000000 / 52131578947369) := by
    rw [show ((52131578947369 / 500000000000) : ℝ) = ((500000000000 / 52131578947369) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15076_neg : (136821287 / 200000000) ≤ -Real.log (500 / 991) ∧
    -Real.log (500 / 991) ≤ (171026609 / 250000000) := by
  have h := checkLog_sound (w := (491 / 1491)) (n := 12)
    (lo := (136821287 / 200000000)) (hi := (171026609 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((991 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(991 / 500) = 1/(500 / 991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15076 : Bounds (136821287 / 200000000) (171026609 / 250000000) (Real.log (991 / 500)) := by
  have h := reflection_log_15076_neg
  have he : Real.log (991 / 500) = -Real.log (500 / 991) := by
    rw [show ((991 / 500) : ℝ) = ((500 / 991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15077_neg : (2008691759 / 500000000) ≤ -Real.log (9 / 500) ∧
    -Real.log (9 / 500) ≤ (1004345881 / 250000000) := by
  have h := checkLog_sound (w := (53 / 197)) (n := 12)
    (lo := (275823809 / 500000000)) (hi := (551647619 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 72) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 72) = 1/(9 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15077 : Bounds (-1004345881 / 250000000) (-2008691759 / 500000000) (Real.log (9 / 500)) := by
  have h := reflection_log_15077_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15078_neg : (490759 / 500000000) ≤ -Real.log (500000 / 500491) ∧
    -Real.log (500000 / 500491) ≤ (981519 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 1000491)) (n := 12)
    (lo := (490759 / 500000000)) (hi := (981519 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500491 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500491 / 500000) = 1/(500000 / 500491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15078 : Bounds (490759 / 500000000) (981519 / 1000000000) (Real.log (500491 / 500000)) := by
  have h := reflection_log_15078_neg
  have he : Real.log (500491 / 500000) = -Real.log (500000 / 500491) := by
    rw [show ((500491 / 500000) : ℝ) = ((500000 / 500491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15079_neg : (491241 / 500000000) ≤ -Real.log (499509 / 500000) ∧
    -Real.log (499509 / 500000) ≤ (982483 / 1000000000) := by
  have h := checkLog_sound (w := (491 / 999509)) (n := 12)
    (lo := (491241 / 500000000)) (hi := (982483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499509) = 1/(499509 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15079 : Bounds (-982483 / 1000000000) (-491241 / 500000000) (Real.log (499509 / 500000)) := by
  have h := reflection_log_15079_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15080_neg : (488085413 / 1000000000) ≤ -Real.log (500000 / 814597) ∧
    -Real.log (500000 / 814597) ≤ (244042707 / 500000000) := by
  have h := checkLog_sound (w := (314597 / 1314597)) (n := 12)
    (lo := (488085413 / 1000000000)) (hi := (244042707 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((814597 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(814597 / 500000) = 1/(500000 / 814597) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15080 : Bounds (488085413 / 1000000000) (244042707 / 500000000) (Real.log (814597 / 500000)) := by
  have h := reflection_log_15080_neg
  have he : Real.log (814597 / 500000) = -Real.log (500000 / 814597) := by
    rw [show ((814597 / 500000) : ℝ) = ((500000 / 814597) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15081_neg : (992076263 / 1000000000) ≤ -Real.log (185403 / 500000) ∧
    -Real.log (185403 / 500000) ≤ (198415253 / 200000000) := by
  have h := checkLog_sound (w := (64597 / 435403)) (n := 12)
    (lo := (298929083 / 1000000000)) (hi := (74732271 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 185403) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 185403) = 1/(185403 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15081 : Bounds (-198415253 / 200000000) (-992076263 / 1000000000) (Real.log (185403 / 500000)) := by
  have h := reflection_log_15081_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15082_neg : (30580637 / 62500000) ≤ -Real.log (500000 / 815579) ∧
    -Real.log (500000 / 815579) ≤ (489290193 / 1000000000) := by
  have h := checkLog_sound (w := (315579 / 1315579)) (n := 12)
    (lo := (30580637 / 62500000)) (hi := (489290193 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((815579 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(815579 / 500000) = 1/(500000 / 815579) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15082 : Bounds (30580637 / 62500000) (489290193 / 1000000000) (Real.log (815579 / 500000)) := by
  have h := reflection_log_15082_neg
  have he : Real.log (815579 / 500000) = -Real.log (500000 / 815579) := by
    rw [show ((815579 / 500000) : ℝ) = ((500000 / 815579) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15083_neg : (99738691 / 100000000) ≤ -Real.log (184421 / 500000) ∧
    -Real.log (184421 / 500000) ≤ (31168341 / 31250000) := by
  have h := checkLog_sound (w := (65579 / 434421)) (n := 12)
    (lo := (30423973 / 100000000)) (hi := (304239731 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 184421) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 184421) = 1/(184421 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15083 : Bounds (-31168341 / 31250000) (-99738691 / 100000000) (Real.log (184421 / 500000)) := by
  have h := reflection_log_15083_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15084_neg : (254048359 / 500000000) ≤ -Real.log (150409894759 / 250000000000) ∧
    -Real.log (150409894759 / 250000000000) ≤ (508096719 / 1000000000) := by
  have h := checkLog_sound (w := (99590105241 / 400409894759)) (n := 12)
    (lo := (254048359 / 500000000)) (hi := (508096719 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 150409894759) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 150409894759) = 1/(150409894759 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15084 : Bounds (-508096719 / 1000000000) (-254048359 / 500000000) (Real.log (150409894759 / 250000000000)) := by
  have h := reflection_log_15084_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15085_neg : (10079817 / 20000000) ≤ -Real.log (151028727591 / 250000000000) ∧
    -Real.log (151028727591 / 250000000000) ≤ (503990851 / 1000000000) := by
  have h := checkLog_sound (w := (98971272409 / 401028727591)) (n := 12)
    (lo := (10079817 / 20000000)) (hi := (503990851 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 151028727591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 151028727591) = 1/(151028727591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15085 : Bounds (-503990851 / 1000000000) (-10079817 / 20000000) (Real.log (151028727591 / 250000000000)) := by
  have h := reflection_log_15085_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15086_neg : (1480161677 / 1000000000) ≤ -Real.log (500000000000 / 2196827990917) ∧
    -Real.log (500000000000 / 2196827990917) ≤ (18502021 / 12500000) := by
  have h := checkLog_sound (w := (196827990917 / 4196827990917)) (n := 12)
    (lo := (93867317 / 1000000000)) (hi := (46933659 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2196827990917 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2196827990917 / 2000000000000) = 1/(500000000000 / 2196827990917) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15086 : Bounds (1480161677 / 1000000000) (18502021 / 12500000) (Real.log (2196827990917 / 500000000000)) := by
  have h := reflection_log_15086_neg
  have he : Real.log (2196827990917 / 500000000000) = -Real.log (500000000000 / 2196827990917) := by
    rw [show ((2196827990917 / 500000000000) : ℝ) = ((500000000000 / 2196827990917) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15087_neg : (1486677101 / 1000000000) ≤ -Real.log (500000000000 / 2211187988353) ∧
    -Real.log (500000000000 / 2211187988353) ≤ (92917319 / 62500000) := by
  have h := checkLog_sound (w := (211187988353 / 4211187988353)) (n := 12)
    (lo := (100382741 / 1000000000)) (hi := (50191371 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2211187988353 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2211187988353 / 2000000000000) = 1/(500000000000 / 2211187988353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15087 : Bounds (1486677101 / 1000000000) (92917319 / 62500000) (Real.log (2211187988353 / 500000000000)) := by
  have h := reflection_log_15087_neg
  have he : Real.log (2211187988353 / 500000000000) = -Real.log (500000000000 / 2211187988353) := by
    rw [show ((2211187988353 / 500000000000) : ℝ) = ((500000000000 / 2211187988353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15088_neg : (290432379 / 62500000) ≤ -Real.log (62500000000 / 6516447368421) ∧
    -Real.log (62500000000 / 6516447368421) ≤ (4646918071 / 1000000000) := by
  have h := checkLog_sound (w := (2516447368421 / 10516447368421)) (n := 12)
    (lo := (61004373 / 125000000)) (hi := (97606997 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6516447368421 / 4000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(6516447368421 / 4000000000000) = 1/(62500000000 / 6516447368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15088 : Bounds (290432379 / 62500000) (4646918071 / 1000000000) (Real.log (6516447368421 / 62500000000)) := by
  have h := reflection_log_15088_neg
  have he : Real.log (6516447368421 / 62500000000) = -Real.log (62500000000 / 6516447368421) := by
    rw [show ((6516447368421 / 62500000000) : ℝ) = ((62500000000 / 6516447368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15089_neg : (4701489953 / 1000000000) ≤ -Real.log (125000000000 / 13763888888889) ∧
    -Real.log (125000000000 / 13763888888889) ≤ (117537249 / 25000000) := by
  have h := checkLog_sound (w := (5763888888889 / 21763888888889)) (n := 12)
    (lo := (542606873 / 1000000000)) (hi := (271303437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((13763888888889 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(13763888888889 / 8000000000000) = 1/(125000000000 / 13763888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15089 : Bounds (4701489953 / 1000000000) (117537249 / 25000000) (Real.log (13763888888889 / 125000000000)) := by
  have h := reflection_log_15089_neg
  have he : Real.log (13763888888889 / 125000000000) = -Real.log (125000000000 / 13763888888889) := by
    rw [show ((13763888888889 / 125000000000) : ℝ) = ((125000000000 / 13763888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15090_neg : (684610849 / 1000000000) ≤ -Real.log (1000 / 1983) ∧
    -Real.log (1000 / 1983) ≤ (13692217 / 20000000) := by
  have h := checkLog_sound (w := (983 / 2983)) (n := 12)
    (lo := (684610849 / 1000000000)) (hi := (13692217 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1983 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1983 / 1000) = 1/(1000 / 1983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15090 : Bounds (684610849 / 1000000000) (13692217 / 20000000) (Real.log (1983 / 1000)) := by
  have h := reflection_log_15090_neg
  have he : Real.log (1983 / 1000) = -Real.log (1000 / 1983) := by
    rw [show ((1983 / 1000) : ℝ) = ((1000 / 1983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15091_neg : (1018635483 / 250000000) ≤ -Real.log (17 / 1000) ∧
    -Real.log (17 / 1000) ≤ (2037270969 / 500000000) := by
  have h := checkLog_sound (w := (57 / 193)) (n := 12)
    (lo := (38050377 / 62500000)) (hi := (608806033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 68) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 68) = 1/(17 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15091 : Bounds (-2037270969 / 500000000) (-1018635483 / 250000000) (Real.log (17 / 1000)) := by
  have h := reflection_log_15091_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15092_neg : (982517 / 1000000000) ≤ -Real.log (1000000 / 1000983) ∧
    -Real.log (1000000 / 1000983) ≤ (491259 / 500000000) := by
  have h := checkLog_sound (w := (983 / 2000983)) (n := 12)
    (lo := (982517 / 1000000000)) (hi := (491259 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000983 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000983 / 1000000) = 1/(1000000 / 1000983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15092 : Bounds (982517 / 1000000000) (491259 / 500000000) (Real.log (1000983 / 1000000)) := by
  have h := reflection_log_15092_neg
  have he : Real.log (1000983 / 1000000) = -Real.log (1000000 / 1000983) := by
    rw [show ((1000983 / 1000000) : ℝ) = ((1000000 / 1000983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15093_neg : (983483 / 1000000000) ≤ -Real.log (999017 / 1000000) ∧
    -Real.log (999017 / 1000000) ≤ (245871 / 250000000) := by
  have h := checkLog_sound (w := (983 / 1999017)) (n := 12)
    (lo := (983483 / 1000000000)) (hi := (245871 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999017) = 1/(999017 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15093 : Bounds (-245871 / 250000000) (-983483 / 1000000000) (Real.log (999017 / 1000000)) := by
  have h := reflection_log_15093_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15094_neg : (488898369 / 1000000000) ≤ -Real.log (1000000 / 1630519) ∧
    -Real.log (1000000 / 1630519) ≤ (48889837 / 100000000) := by
  have h := checkLog_sound (w := (630519 / 2630519)) (n := 12)
    (lo := (488898369 / 1000000000)) (hi := (48889837 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1630519 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1630519 / 1000000) = 1/(1000000 / 1630519) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15094 : Bounds (488898369 / 1000000000) (48889837 / 100000000) (Real.log (1630519 / 1000000)) := by
  have h := reflection_log_15094_neg
  have he : Real.log (1630519 / 1000000) = -Real.log (1000000 / 1630519) := by
    rw [show ((1630519 / 1000000) : ℝ) = ((1000000 / 1630519) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15095_neg : (24891399 / 25000000) ≤ -Real.log (369481 / 1000000) ∧
    -Real.log (369481 / 1000000) ≤ (497827981 / 500000000) := by
  have h := checkLog_sound (w := (130519 / 869481)) (n := 12)
    (lo := (15125439 / 50000000)) (hi := (302508781 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 369481) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 369481) = 1/(369481 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15095 : Bounds (-497827981 / 500000000) (-24891399 / 25000000) (Real.log (369481 / 1000000)) := by
  have h := reflection_log_15095_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15096_neg : (245054453 / 500000000) ≤ -Real.log (500000 / 816247) ∧
    -Real.log (500000 / 816247) ≤ (490108907 / 1000000000) := by
  have h := checkLog_sound (w := (316247 / 1316247)) (n := 12)
    (lo := (245054453 / 500000000)) (hi := (490108907 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((816247 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(816247 / 500000) = 1/(500000 / 816247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15096 : Bounds (245054453 / 500000000) (490108907 / 1000000000) (Real.log (816247 / 500000)) := by
  have h := reflection_log_15096_neg
  have he : Real.log (816247 / 500000) = -Real.log (500000 / 816247) := by
    rw [show ((816247 / 500000) : ℝ) = ((500000 / 816247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15097_neg : (1001015633 / 1000000000) ≤ -Real.log (183753 / 500000) ∧
    -Real.log (183753 / 500000) ≤ (200203127 / 200000000) := by
  have h := checkLog_sound (w := (66247 / 433753)) (n := 12)
    (lo := (307868453 / 1000000000)) (hi := (153934227 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 183753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 183753) = 1/(183753 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15097 : Bounds (-200203127 / 200000000) (-1001015633 / 1000000000) (Real.log (183753 / 500000)) := by
  have h := reflection_log_15097_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15098_neg : (510906727 / 1000000000) ≤ -Real.log (149987834991 / 250000000000) ∧
    -Real.log (149987834991 / 250000000000) ≤ (63863341 / 125000000) := by
  have h := checkLog_sound (w := (100012165009 / 399987834991)) (n := 12)
    (lo := (510906727 / 1000000000)) (hi := (63863341 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 149987834991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 149987834991) = 1/(149987834991 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15098 : Bounds (-63863341 / 125000000) (-510906727 / 1000000000) (Real.log (149987834991 / 250000000000)) := by
  have h := reflection_log_15098_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15099_neg : (506757591 / 1000000000) ≤ -Real.log (602445790639 / 1000000000000) ∧
    -Real.log (602445790639 / 1000000000000) ≤ (63344699 / 125000000) := by
  have h := checkLog_sound (w := (397554209361 / 1602445790639)) (n := 12)
    (lo := (506757591 / 1000000000)) (hi := (63344699 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 602445790639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 602445790639) = 1/(602445790639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15099 : Bounds (-63344699 / 125000000) (-506757591 / 1000000000) (Real.log (602445790639 / 1000000000000)) := by
  have h := reflection_log_15099_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15100_neg : (185569291 / 125000000) ≤ -Real.log (62500000000 / 275812389541) ∧
    -Real.log (62500000000 / 275812389541) ≤ (1484554331 / 1000000000) := by
  have h := checkLog_sound (w := (25812389541 / 525812389541)) (n := 12)
    (lo := (191914 / 1953125)) (hi := (98259969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((275812389541 / 250000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(275812389541 / 250000000000) = 1/(62500000000 / 275812389541) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15100 : Bounds (185569291 / 125000000) (1484554331 / 1000000000) (Real.log (275812389541 / 62500000000)) := by
  have h := reflection_log_15100_neg
  have he : Real.log (275812389541 / 62500000000) = -Real.log (62500000000 / 275812389541) := by
    rw [show ((275812389541 / 62500000000) : ℝ) = ((62500000000 / 275812389541) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15101_neg : (1491124539 / 1000000000) ≤ -Real.log (250000000000 / 1110522005083) ∧
    -Real.log (250000000000 / 1110522005083) ≤ (745562271 / 500000000) := by
  have h := checkLog_sound (w := (110522005083 / 2110522005083)) (n := 12)
    (lo := (104830179 / 1000000000)) (hi := (5241509 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1110522005083 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1110522005083 / 1000000000000) = 1/(250000000000 / 1110522005083) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15101 : Bounds (1491124539 / 1000000000) (745562271 / 500000000) (Real.log (1110522005083 / 250000000000)) := by
  have h := reflection_log_15101_neg
  have he : Real.log (1110522005083 / 250000000000) = -Real.log (250000000000 / 1110522005083) := by
    rw [show ((1110522005083 / 250000000000) : ℝ) = ((250000000000 / 1110522005083) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15102_neg : (4701489953 / 1000000000) ≤ -Real.log (100000000000 / 11011111111111) ∧
    -Real.log (100000000000 / 11011111111111) ≤ (117537249 / 25000000) := by
  have h := checkLog_sound (w := (4611111111111 / 17411111111111)) (n := 12)
    (lo := (542606873 / 1000000000)) (hi := (271303437 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11011111111111 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11011111111111 / 6400000000000) = 1/(100000000000 / 11011111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15102 : Bounds (4701489953 / 1000000000) (117537249 / 25000000) (Real.log (11011111111111 / 100000000000)) := by
  have h := reflection_log_15102_neg
  have he : Real.log (11011111111111 / 100000000000) = -Real.log (100000000000 / 11011111111111) := by
    rw [show ((11011111111111 / 100000000000) : ℝ) = ((100000000000 / 11011111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15103_neg : (4759152781 / 1000000000) ≤ -Real.log (100000000000 / 11664705882353) ∧
    -Real.log (100000000000 / 11664705882353) ≤ (1189788197 / 250000000) := by
  have h := checkLog_sound (w := (5264705882353 / 18064705882353)) (n := 12)
    (lo := (600269701 / 1000000000)) (hi := (300134851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11664705882353 / 6400000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(11664705882353 / 6400000000000) = 1/(100000000000 / 11664705882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15103 : Bounds (4759152781 / 1000000000) (1189788197 / 250000000) (Real.log (11664705882353 / 100000000000)) := by
  have h := reflection_log_15103_neg
  have he : Real.log (11664705882353 / 100000000000) = -Real.log (100000000000 / 11664705882353) := by
    rw [show ((11664705882353 / 100000000000) : ℝ) = ((100000000000 / 11664705882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0236 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15104_neg : (5352461 / 7812500) ≤ -Real.log (125 / 248) ∧
    -Real.log (125 / 248) ≤ (685115009 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 373)) (n := 12)
    (lo := (5352461 / 7812500)) (hi := (685115009 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((248 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(248 / 125) = 1/(125 / 248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15104 : Bounds (5352461 / 7812500) (685115009 / 1000000000) (Real.log (248 / 125)) := by
  have h := reflection_log_15104_neg
  have he : Real.log (248 / 125) = -Real.log (125 / 248) := by
    rw [show ((248 / 125) : ℝ) = ((125 / 248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15105_neg : (4135166553 / 1000000000) ≤ -Real.log (2 / 125) ∧
    -Real.log (2 / 125) ≤ (4135166559 / 1000000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 5 (by norm_num)
  have hq : (2 : ℝ)^5*(125 / 64) = 1/(2 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15105 : Bounds (-4135166559 / 1000000000) (-4135166553 / 1000000000) (Real.log (2 / 125)) := by
  have h := reflection_log_15105_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15106_neg : (245879 / 250000000) ≤ -Real.log (125000 / 125123) ∧
    -Real.log (125000 / 125123) ≤ (983517 / 1000000000) := by
  have h := checkLog_sound (w := (123 / 250123)) (n := 12)
    (lo := (245879 / 250000000)) (hi := (983517 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125123 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125123 / 125000) = 1/(125000 / 125123) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15106 : Bounds (245879 / 250000000) (983517 / 1000000000) (Real.log (125123 / 125000)) := by
  have h := reflection_log_15106_neg
  have he : Real.log (125123 / 125000) = -Real.log (125000 / 125123) := by
    rw [show ((125123 / 125000) : ℝ) = ((125000 / 125123) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15107_neg : (246121 / 250000000) ≤ -Real.log (124877 / 125000) ∧
    -Real.log (124877 / 125000) ≤ (196897 / 200000000) := by
  have h := checkLog_sound (w := (123 / 249877)) (n := 12)
    (lo := (246121 / 250000000)) (hi := (196897 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 124877) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 124877) = 1/(124877 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15107 : Bounds (-196897 / 200000000) (-246121 / 250000000) (Real.log (124877 / 125000)) := by
  have h := reflection_log_15107_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15108_neg : (48971863 / 100000000) ≤ -Real.log (1000000 / 1631857) ∧
    -Real.log (1000000 / 1631857) ≤ (489718631 / 1000000000) := by
  have h := checkLog_sound (w := (631857 / 2631857)) (n := 12)
    (lo := (48971863 / 100000000)) (hi := (489718631 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1631857 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1631857 / 1000000) = 1/(1000000 / 1631857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15108 : Bounds (48971863 / 100000000) (489718631 / 1000000000) (Real.log (1631857 / 1000000)) := by
  have h := reflection_log_15108_neg
  have he : Real.log (1631857 / 1000000) = -Real.log (1000000 / 1631857) := by
    rw [show ((1631857 / 1000000) : ℝ) = ((1000000 / 1631857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15109_neg : (249820957 / 250000000) ≤ -Real.log (368143 / 1000000) ∧
    -Real.log (368143 / 1000000) ≤ (99928383 / 100000000) := by
  have h := checkLog_sound (w := (131857 / 868143)) (n := 12)
    (lo := (38267081 / 125000000)) (hi := (306136649 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 368143) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 368143) = 1/(368143 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15109 : Bounds (-99928383 / 100000000) (-249820957 / 250000000) (Real.log (368143 / 1000000)) := by
  have h := reflection_log_15109_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15110_neg : (122734033 / 250000000) ≤ -Real.log (200000 / 326769) ∧
    -Real.log (200000 / 326769) ≤ (490936133 / 1000000000) := by
  have h := checkLog_sound (w := (126769 / 526769)) (n := 12)
    (lo := (122734033 / 250000000)) (hi := (490936133 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((326769 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(326769 / 200000) = 1/(200000 / 326769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15110 : Bounds (122734033 / 250000000) (490936133 / 1000000000) (Real.log (326769 / 200000)) := by
  have h := reflection_log_15110_neg
  have he : Real.log (326769 / 200000) = -Real.log (200000 / 326769) := by
    rw [show ((326769 / 200000) : ℝ) = ((200000 / 326769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15111_neg : (1004698537 / 1000000000) ≤ -Real.log (73231 / 200000) ∧
    -Real.log (73231 / 200000) ≤ (1004698539 / 1000000000) := by
  have h := checkLog_sound (w := (26769 / 173231)) (n := 12)
    (lo := (311551357 / 1000000000)) (hi := (155775679 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 73231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 73231) = 1/(73231 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15111 : Bounds (-1004698539 / 1000000000) (-1004698537 / 1000000000) (Real.log (73231 / 200000)) := by
  have h := reflection_log_15111_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15112_neg : (102752481 / 200000000) ≤ -Real.log (23929620639 / 40000000000) ∧
    -Real.log (23929620639 / 40000000000) ≤ (256881203 / 500000000) := by
  have h := checkLog_sound (w := (16070379361 / 63929620639)) (n := 12)
    (lo := (102752481 / 200000000)) (hi := (256881203 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23929620639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23929620639) = 1/(23929620639 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15112 : Bounds (-256881203 / 500000000) (-102752481 / 200000000) (Real.log (23929620639 / 40000000000)) := by
  have h := reflection_log_15112_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15113_neg : (509565199 / 1000000000) ≤ -Real.log (600756731551 / 1000000000000) ∧
    -Real.log (600756731551 / 1000000000000) ≤ (1273913 / 2500000) := by
  have h := checkLog_sound (w := (399243268449 / 1600756731551)) (n := 12)
    (lo := (509565199 / 1000000000)) (hi := (1273913 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 600756731551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 600756731551) = 1/(600756731551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15113 : Bounds (-1273913 / 2500000) (-509565199 / 1000000000) (Real.log (600756731551 / 1000000000000)) := by
  have h := reflection_log_15113_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15114_neg : (744501229 / 500000000) ≤ -Real.log (500000000000 / 2216335771697) ∧
    -Real.log (500000000000 / 2216335771697) ≤ (1489002461 / 1000000000) := by
  have h := checkLog_sound (w := (216335771697 / 4216335771697)) (n := 12)
    (lo := (51354049 / 500000000)) (hi := (102708099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2216335771697 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2216335771697 / 2000000000000) = 1/(500000000000 / 2216335771697) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15114 : Bounds (744501229 / 500000000) (1489002461 / 1000000000) (Real.log (2216335771697 / 500000000000)) := by
  have h := reflection_log_15114_neg
  have he : Real.log (2216335771697 / 500000000000) = -Real.log (500000000000 / 2216335771697) := by
    rw [show ((2216335771697 / 500000000000) : ℝ) = ((500000000000 / 2216335771697) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15115_neg : (1495634669 / 1000000000) ≤ -Real.log (500000000000 / 2231083830619) ∧
    -Real.log (500000000000 / 2231083830619) ≤ (93477167 / 62500000) := by
  have h := checkLog_sound (w := (231083830619 / 4231083830619)) (n := 12)
    (lo := (109340309 / 1000000000)) (hi := (10934031 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2231083830619 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2231083830619 / 2000000000000) = 1/(500000000000 / 2231083830619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15115 : Bounds (1495634669 / 1000000000) (93477167 / 62500000) (Real.log (2231083830619 / 500000000000)) := by
  have h := reflection_log_15115_neg
  have he : Real.log (2231083830619 / 500000000000) = -Real.log (500000000000 / 2231083830619) := by
    rw [show ((2231083830619 / 500000000000) : ℝ) = ((500000000000 / 2231083830619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15116_neg : (4759152781 / 1000000000) ≤ -Real.log (125000000000 / 14580882352941) ∧
    -Real.log (125000000000 / 14580882352941) ≤ (1189788197 / 250000000) := by
  have h := checkLog_sound (w := (6580882352941 / 22580882352941)) (n := 12)
    (lo := (600269701 / 1000000000)) (hi := (300134851 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((14580882352941 / 8000000000000) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(14580882352941 / 8000000000000) = 1/(125000000000 / 14580882352941) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15116 : Bounds (4759152781 / 1000000000) (1189788197 / 250000000) (Real.log (14580882352941 / 125000000000)) := by
  have h := reflection_log_15116_neg
  have he : Real.log (14580882352941 / 125000000000) = -Real.log (125000000000 / 14580882352941) := by
    rw [show ((14580882352941 / 125000000000) : ℝ) = ((125000000000 / 14580882352941) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15117_neg : (2410140781 / 500000000) ≤ -Real.log (1 / 124) ∧
    -Real.log (1 / 124) ≤ (4820281569 / 1000000000) := by
  have h := checkLog_sound (w := (15 / 47)) (n := 12)
    (lo := (330699241 / 500000000)) (hi := (661398483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31 / 16) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(31 / 16) = 1/(1 / 124) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15117 : Bounds (2410140781 / 500000000) (4820281569 / 1000000000) (Real.log (124 / 1)) := by
  have h := reflection_log_15117_neg
  have he : Real.log (124 / 1) = -Real.log (1 / 124) := by
    rw [show ((124 / 1) : ℝ) = ((1 / 124) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15118_neg : (342809457 / 500000000) ≤ -Real.log (200 / 397) ∧
    -Real.log (200 / 397) ≤ (137123783 / 200000000) := by
  have h := checkLog_sound (w := (197 / 597)) (n := 12)
    (lo := (342809457 / 500000000)) (hi := (137123783 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((397 / 200) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(397 / 200) = 1/(200 / 397) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15118 : Bounds (342809457 / 500000000) (137123783 / 200000000) (Real.log (397 / 200)) := by
  have h := reflection_log_15118_neg
  have he : Real.log (397 / 200) = -Real.log (200 / 397) := by
    rw [show ((397 / 200) : ℝ) = ((200 / 397) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15119_neg : (2099852537 / 500000000) ≤ -Real.log (3 / 200) ∧
    -Real.log (3 / 200) ≤ (4199705081 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 49)) (n := 12)
    (lo := (20410997 / 500000000)) (hi := (8164399 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 24) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25 / 24) = 1/(3 / 200) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15119 : Bounds (-4199705081 / 1000000000) (-2099852537 / 500000000) (Real.log (3 / 200)) := by
  have h := reflection_log_15119_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15120_neg : (196903 / 200000000) ≤ -Real.log (200000 / 200197) ∧
    -Real.log (200000 / 200197) ≤ (246129 / 250000000) := by
  have h := checkLog_sound (w := (197 / 400197)) (n := 12)
    (lo := (196903 / 200000000)) (hi := (246129 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200197 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200197 / 200000) = 1/(200000 / 200197) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15120 : Bounds (196903 / 200000000) (246129 / 250000000) (Real.log (200197 / 200000)) := by
  have h := reflection_log_15120_neg
  have he : Real.log (200197 / 200000) = -Real.log (200000 / 200197) := by
    rw [show ((200197 / 200000) : ℝ) = ((200000 / 200197) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15121_neg : (197097 / 200000000) ≤ -Real.log (199803 / 200000) ∧
    -Real.log (199803 / 200000) ≤ (492743 / 500000000) := by
  have h := checkLog_sound (w := (197 / 399803)) (n := 12)
    (lo := (197097 / 200000000)) (hi := (492743 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 199803) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 199803) = 1/(199803 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15121 : Bounds (-492743 / 500000000) (-197097 / 200000000) (Real.log (199803 / 200000)) := by
  have h := reflection_log_15121_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15122_neg : (245273089 / 500000000) ≤ -Real.log (125000 / 204151) ∧
    -Real.log (125000 / 204151) ≤ (490546179 / 1000000000) := by
  have h := checkLog_sound (w := (79151 / 329151)) (n := 12)
    (lo := (245273089 / 500000000)) (hi := (490546179 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((204151 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(204151 / 125000) = 1/(125000 / 204151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15122 : Bounds (245273089 / 500000000) (490546179 / 1000000000) (Real.log (204151 / 125000)) := by
  have h := reflection_log_15122_neg
  have he : Real.log (204151 / 125000) = -Real.log (125000 / 204151) := by
    rw [show ((204151 / 125000) : ℝ) = ((125000 / 204151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15123_neg : (250740087 / 250000000) ≤ -Real.log (45849 / 125000) ∧
    -Real.log (45849 / 125000) ≤ (20059207 / 20000000) := by
  have h := checkLog_sound (w := (16651 / 108349)) (n := 12)
    (lo := (19363323 / 62500000)) (hi := (309813169 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 45849) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 45849) = 1/(45849 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15123 : Bounds (-20059207 / 20000000) (-250740087 / 250000000) (Real.log (45849 / 125000)) := by
  have h := reflection_log_15123_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15124_neg : (122942809 / 250000000) ≤ -Real.log (100000 / 163521) ∧
    -Real.log (100000 / 163521) ≤ (491771237 / 1000000000) := by
  have h := checkLog_sound (w := (63521 / 263521)) (n := 12)
    (lo := (122942809 / 250000000)) (hi := (491771237 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163521 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163521 / 100000) = 1/(100000 / 163521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15124 : Bounds (122942809 / 250000000) (491771237 / 1000000000) (Real.log (163521 / 100000)) := by
  have h := reflection_log_15124_neg
  have he : Real.log (163521 / 100000) = -Real.log (100000 / 163521) := by
    rw [show ((163521 / 100000) : ℝ) = ((100000 / 163521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15125_neg : (126054179 / 125000000) ≤ -Real.log (36479 / 100000) ∧
    -Real.log (36479 / 100000) ≤ (504216717 / 500000000) := by
  have h := checkLog_sound (w := (13521 / 86479)) (n := 12)
    (lo := (78821563 / 250000000)) (hi := (315286253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36479) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36479) = 1/(36479 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15125 : Bounds (-504216717 / 500000000) (-126054179 / 125000000) (Real.log (36479 / 100000)) := by
  have h := reflection_log_15125_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15126_neg : (129165549 / 250000000) ≤ -Real.log (5965082559 / 10000000000) ∧
    -Real.log (5965082559 / 10000000000) ≤ (516662197 / 1000000000) := by
  have h := checkLog_sound (w := (4034917441 / 15965082559)) (n := 12)
    (lo := (129165549 / 250000000)) (hi := (516662197 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5965082559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5965082559) = 1/(5965082559 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15126 : Bounds (-516662197 / 1000000000) (-129165549 / 250000000) (Real.log (5965082559 / 10000000000)) := by
  have h := reflection_log_15126_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15127_neg : (51241417 / 100000000) ≤ -Real.log (9360119199 / 15625000000) ∧
    -Real.log (9360119199 / 15625000000) ≤ (512414171 / 1000000000) := by
  have h := checkLog_sound (w := (6264880801 / 24985119199)) (n := 12)
    (lo := (51241417 / 100000000)) (hi := (512414171 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 9360119199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 9360119199) = 1/(9360119199 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15127 : Bounds (-512414171 / 1000000000) (-51241417 / 100000000) (Real.log (9360119199 / 15625000000)) := by
  have h := reflection_log_15127_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15128_neg : (746753263 / 500000000) ≤ -Real.log (125000000000 / 556585203603) ∧
    -Real.log (125000000000 / 556585203603) ≤ (1493506529 / 1000000000) := by
  have h := checkLog_sound (w := (56585203603 / 1056585203603)) (n := 12)
    (lo := (53606083 / 500000000)) (hi := (107212167 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((556585203603 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(556585203603 / 500000000000) = 1/(125000000000 / 556585203603) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15128 : Bounds (746753263 / 500000000) (1493506529 / 1000000000) (Real.log (556585203603 / 125000000000)) := by
  have h := reflection_log_15128_neg
  have he : Real.log (556585203603 / 125000000000) = -Real.log (125000000000 / 556585203603) := by
    rw [show ((556585203603 / 125000000000) : ℝ) = ((125000000000 / 556585203603) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15129_neg : (375051167 / 250000000) ≤ -Real.log (500000000000 / 2241303215549) ∧
    -Real.log (500000000000 / 2241303215549) ≤ (1500204671 / 1000000000) := by
  have h := checkLog_sound (w := (241303215549 / 4241303215549)) (n := 12)
    (lo := (28477577 / 250000000)) (hi := (113910309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2241303215549 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2241303215549 / 2000000000000) = 1/(500000000000 / 2241303215549) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15129 : Bounds (375051167 / 250000000) (1500204671 / 1000000000) (Real.log (2241303215549 / 500000000000)) := by
  have h := reflection_log_15129_neg
  have he : Real.log (2241303215549 / 500000000000) = -Real.log (500000000000 / 2241303215549) := by
    rw [show ((2241303215549 / 500000000000) : ℝ) = ((500000000000 / 2241303215549) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15130_neg : (1221330997 / 250000000) ≤ -Real.log (500000000000 / 66166666666667) ∧
    -Real.log (500000000000 / 66166666666667) ≤ (1221330999 / 250000000) := by
  have h := checkLog_sound (w := (2166666666667 / 130166666666667)) (n := 12)
    (lo := (1040429 / 31250000)) (hi := (33293729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((66166666666667 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(66166666666667 / 64000000000000) = 1/(500000000000 / 66166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15130 : Bounds (1221330997 / 250000000) (1221330999 / 250000000) (Real.log (66166666666667 / 500000000000)) := by
  have h := reflection_log_15130_neg
  have he : Real.log (66166666666667 / 500000000000) = -Real.log (500000000000 / 66166666666667) := by
    rw [show ((66166666666667 / 500000000000) : ℝ) = ((500000000000 / 66166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15131_neg : (137224513 / 200000000) ≤ -Real.log (500 / 993) ∧
    -Real.log (500 / 993) ≤ (343061283 / 500000000) := by
  have h := checkLog_sound (w := (493 / 1493)) (n := 12)
    (lo := (137224513 / 200000000)) (hi := (343061283 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((993 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(993 / 500) = 1/(500 / 993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15131 : Bounds (137224513 / 200000000) (343061283 / 500000000) (Real.log (993 / 500)) := by
  have h := reflection_log_15131_neg
  have he : Real.log (993 / 500) = -Real.log (500 / 993) := by
    rw [show ((993 / 500) : ℝ) = ((500 / 993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15132_neg : (2134348973 / 500000000) ≤ -Real.log (7 / 500) ∧
    -Real.log (7 / 500) ≤ (4268697953 / 1000000000) := by
  have h := checkLog_sound (w := (13 / 237)) (n := 12)
    (lo := (54907433 / 500000000)) (hi := (109814867 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 112) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 112) = 1/(7 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15132 : Bounds (-4268697953 / 1000000000) (-2134348973 / 500000000) (Real.log (7 / 500)) := by
  have h := reflection_log_15132_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15133_neg : (492757 / 500000000) ≤ -Real.log (500000 / 500493) ∧
    -Real.log (500000 / 500493) ≤ (197103 / 200000000) := by
  have h := checkLog_sound (w := (493 / 1000493)) (n := 12)
    (lo := (492757 / 500000000)) (hi := (197103 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500493 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500493 / 500000) = 1/(500000 / 500493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15133 : Bounds (492757 / 500000000) (197103 / 200000000) (Real.log (500493 / 500000)) := by
  have h := reflection_log_15133_neg
  have he : Real.log (500493 / 500000) = -Real.log (500000 / 500493) := by
    rw [show ((500493 / 500000) : ℝ) = ((500000 / 500493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15134_neg : (493243 / 500000000) ≤ -Real.log (499507 / 500000) ∧
    -Real.log (499507 / 500000) ≤ (986487 / 1000000000) := by
  have h := checkLog_sound (w := (493 / 999507)) (n := 12)
    (lo := (493243 / 500000000)) (hi := (986487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499507) = 1/(499507 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15134 : Bounds (-986487 / 1000000000) (-493243 / 500000000) (Real.log (499507 / 500000)) := by
  have h := reflection_log_15134_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15135_neg : (491382219 / 1000000000) ≤ -Real.log (500000 / 817287) ∧
    -Real.log (500000 / 817287) ≤ (24569111 / 50000000) := by
  have h := checkLog_sound (w := (317287 / 1317287)) (n := 12)
    (lo := (491382219 / 1000000000)) (hi := (24569111 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((817287 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(817287 / 500000) = 1/(500000 / 817287) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15135 : Bounds (491382219 / 1000000000) (24569111 / 50000000) (Real.log (817287 / 500000)) := by
  have h := reflection_log_15135_neg
  have he : Real.log (817287 / 500000) = -Real.log (500000 / 817287) := by
    rw [show ((817287 / 500000) : ℝ) = ((500000 / 817287) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15136_neg : (503345741 / 500000000) ≤ -Real.log (182713 / 500000) ∧
    -Real.log (182713 / 500000) ≤ (251672871 / 250000000) := by
  have h := checkLog_sound (w := (67287 / 432713)) (n := 12)
    (lo := (156772151 / 500000000)) (hi := (313544303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 182713) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 182713) = 1/(182713 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15136 : Bounds (-251672871 / 250000000) (-503345741 / 500000000) (Real.log (182713 / 500000)) := by
  have h := reflection_log_15136_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15137_neg : (61576851 / 125000000) ≤ -Real.log (100000 / 163659) ∧
    -Real.log (100000 / 163659) ≤ (492614809 / 1000000000) := by
  have h := checkLog_sound (w := (63659 / 263659)) (n := 12)
    (lo := (61576851 / 125000000)) (hi := (492614809 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((163659 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(163659 / 100000) = 1/(100000 / 163659) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15137 : Bounds (61576851 / 125000000) (492614809 / 1000000000) (Real.log (163659 / 100000)) := by
  have h := reflection_log_15137_neg
  have he : Real.log (163659 / 100000) = -Real.log (100000 / 163659) := by
    rw [show ((163659 / 100000) : ℝ) = ((100000 / 163659) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15138_neg : (253055901 / 250000000) ≤ -Real.log (36341 / 100000) ∧
    -Real.log (36341 / 100000) ≤ (506111803 / 500000000) := by
  have h := checkLog_sound (w := (13659 / 86341)) (n := 12)
    (lo := (39884553 / 125000000)) (hi := (12763057 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((50000 / 36341) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(50000 / 36341) = 1/(36341 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15138 : Bounds (-506111803 / 500000000) (-253055901 / 250000000) (Real.log (36341 / 100000)) := by
  have h := reflection_log_15138_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15139_neg : (129902199 / 250000000) ≤ -Real.log (5947531719 / 10000000000) ∧
    -Real.log (5947531719 / 10000000000) ≤ (519608797 / 1000000000) := by
  have h := checkLog_sound (w := (4052468281 / 15947531719)) (n := 12)
    (lo := (129902199 / 250000000)) (hi := (519608797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000000 / 5947531719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000000 / 5947531719) = 1/(5947531719 / 10000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15139 : Bounds (-519608797 / 1000000000) (-129902199 / 250000000) (Real.log (5947531719 / 10000000000)) := by
  have h := reflection_log_15139_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15140_neg : (257654631 / 500000000) ≤ -Real.log (149328959631 / 250000000000) ∧
    -Real.log (149328959631 / 250000000000) ≤ (515309263 / 1000000000) := by
  have h := checkLog_sound (w := (100671040369 / 399328959631)) (n := 12)
    (lo := (257654631 / 500000000)) (hi := (515309263 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 149328959631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 149328959631) = 1/(149328959631 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15140 : Bounds (-515309263 / 1000000000) (-257654631 / 500000000) (Real.log (149328959631 / 250000000000)) := by
  have h := reflection_log_15140_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15141_neg : (1498073701 / 1000000000) ≤ -Real.log (500000000000 / 2236532156989) ∧
    -Real.log (500000000000 / 2236532156989) ≤ (187259213 / 125000000) := by
  have h := checkLog_sound (w := (236532156989 / 4236532156989)) (n := 12)
    (lo := (111779341 / 1000000000)) (hi := (55889671 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2236532156989 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2236532156989 / 2000000000000) = 1/(500000000000 / 2236532156989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15141 : Bounds (1498073701 / 1000000000) (187259213 / 125000000) (Real.log (2236532156989 / 500000000000)) := by
  have h := reflection_log_15141_neg
  have he : Real.log (2236532156989 / 500000000000) = -Real.log (500000000000 / 2236532156989) := by
    rw [show ((2236532156989 / 500000000000) : ℝ) = ((500000000000 / 2236532156989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15142_neg : (1504838413 / 1000000000) ≤ -Real.log (250000000000 / 1125856470653) ∧
    -Real.log (250000000000 / 1125856470653) ≤ (94052401 / 62500000) := by
  have h := checkLog_sound (w := (125856470653 / 2125856470653)) (n := 12)
    (lo := (118544053 / 1000000000)) (hi := (59272027 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1125856470653 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1125856470653 / 1000000000000) = 1/(250000000000 / 1125856470653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15142 : Bounds (1504838413 / 1000000000) (94052401 / 62500000) (Real.log (1125856470653 / 250000000000)) := by
  have h := reflection_log_15142_neg
  have he : Real.log (1125856470653 / 250000000000) = -Real.log (250000000000 / 1125856470653) := by
    rw [show ((1125856470653 / 250000000000) : ℝ) = ((250000000000 / 1125856470653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15143_neg : (1221330997 / 250000000) ≤ -Real.log (250000000000 / 33083333333333) ∧
    -Real.log (250000000000 / 33083333333333) ≤ (1221330999 / 250000000) := by
  have h := checkLog_sound (w := (1083333333333 / 65083333333333)) (n := 12)
    (lo := (1040429 / 31250000)) (hi := (33293729 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((33083333333333 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(33083333333333 / 32000000000000) = 1/(250000000000 / 33083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15143 : Bounds (1221330997 / 250000000) (1221330999 / 250000000) (Real.log (33083333333333 / 250000000000)) := by
  have h := reflection_log_15143_neg
  have he : Real.log (33083333333333 / 250000000000) = -Real.log (250000000000 / 33083333333333) := by
    rw [show ((33083333333333 / 250000000000) : ℝ) = ((250000000000 / 33083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15144_neg : (4954820511 / 1000000000) ≤ -Real.log (125000000000 / 17732142857143) ∧
    -Real.log (125000000000 / 17732142857143) ≤ (4954820519 / 1000000000) := by
  have h := checkLog_sound (w := (1732142857143 / 33732142857143)) (n := 12)
    (lo := (102790251 / 1000000000)) (hi := (25697563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((17732142857143 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(17732142857143 / 16000000000000) = 1/(125000000000 / 17732142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15144 : Bounds (4954820511 / 1000000000) (4954820519 / 1000000000) (Real.log (17732142857143 / 125000000000)) := by
  have h := reflection_log_15144_neg
  have he : Real.log (17732142857143 / 125000000000) = -Real.log (125000000000 / 17732142857143) := by
    rw [show ((17732142857143 / 125000000000) : ℝ) = ((125000000000 / 17732142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15145_neg : (686625963 / 1000000000) ≤ -Real.log (1000 / 1987) ∧
    -Real.log (1000 / 1987) ≤ (171656491 / 250000000) := by
  have h := checkLog_sound (w := (987 / 2987)) (n := 12)
    (lo := (686625963 / 1000000000)) (hi := (171656491 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1987 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1987 / 1000) = 1/(1000 / 1987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15145 : Bounds (686625963 / 1000000000) (171656491 / 250000000) (Real.log (1987 / 1000)) := by
  have h := reflection_log_15145_neg
  have he : Real.log (1987 / 1000) = -Real.log (1000 / 1987) := by
    rw [show ((1987 / 1000) : ℝ) = ((1000 / 1987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15146_neg : (2171402959 / 500000000) ≤ -Real.log (13 / 1000) ∧
    -Real.log (13 / 1000) ≤ (173712237 / 40000000) := by
  have h := checkLog_sound (w := (21 / 229)) (n := 12)
    (lo := (91961419 / 500000000)) (hi := (183922839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 104) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 104) = 1/(13 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15146 : Bounds (-173712237 / 40000000) (-2171402959 / 500000000) (Real.log (13 / 1000)) := by
  have h := reflection_log_15146_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15147_neg : (986513 / 1000000000) ≤ -Real.log (1000000 / 1000987) ∧
    -Real.log (1000000 / 1000987) ≤ (493257 / 500000000) := by
  have h := checkLog_sound (w := (987 / 2000987)) (n := 12)
    (lo := (986513 / 1000000000)) (hi := (493257 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000987 / 1000000) = 1/(1000000 / 1000987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15147 : Bounds (986513 / 1000000000) (493257 / 500000000) (Real.log (1000987 / 1000000)) := by
  have h := reflection_log_15147_neg
  have he : Real.log (1000987 / 1000000) = -Real.log (1000000 / 1000987) := by
    rw [show ((1000987 / 1000000) : ℝ) = ((1000000 / 1000987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15148_neg : (987487 / 1000000000) ≤ -Real.log (999013 / 1000000) ∧
    -Real.log (999013 / 1000000) ≤ (30859 / 31250000) := by
  have h := checkLog_sound (w := (987 / 1999013)) (n := 12)
    (lo := (987487 / 1000000000)) (hi := (30859 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999013) = 1/(999013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15148 : Bounds (-30859 / 31250000) (-987487 / 1000000000) (Real.log (999013 / 1000000)) := by
  have h := reflection_log_15148_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15149_neg : (492226731 / 1000000000) ≤ -Real.log (200000 / 327191) ∧
    -Real.log (200000 / 327191) ≤ (123056683 / 250000000) := by
  have h := checkLog_sound (w := (127191 / 527191)) (n := 12)
    (lo := (492226731 / 1000000000)) (hi := (123056683 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((327191 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(327191 / 200000) = 1/(200000 / 327191) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15149 : Bounds (492226731 / 1000000000) (123056683 / 250000000) (Real.log (327191 / 200000)) := by
  have h := reflection_log_15149_neg
  have he : Real.log (327191 / 200000) = -Real.log (200000 / 327191) := by
    rw [show ((327191 / 200000) : ℝ) = ((200000 / 327191) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15150_neg : (31577431 / 31250000) ≤ -Real.log (72809 / 200000) ∧
    -Real.log (72809 / 200000) ≤ (505238897 / 500000000) := by
  have h := checkLog_sound (w := (27191 / 172809)) (n := 12)
    (lo := (79332653 / 250000000)) (hi := (317330613 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 72809) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 72809) = 1/(72809 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15150 : Bounds (-505238897 / 500000000) (-31577431 / 31250000) (Real.log (72809 / 200000)) := by
  have h := reflection_log_15150_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15151_neg : (30841753 / 62500000) ≤ -Real.log (1000000 / 1637987) ∧
    -Real.log (1000000 / 1637987) ≤ (493468049 / 1000000000) := by
  have h := checkLog_sound (w := (637987 / 2637987)) (n := 12)
    (lo := (30841753 / 62500000)) (hi := (493468049 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1637987 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1637987 / 1000000) = 1/(1000000 / 1637987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15151 : Bounds (30841753 / 62500000) (493468049 / 1000000000) (Real.log (1637987 / 1000000)) := by
  have h := reflection_log_15151_neg
  have he : Real.log (1637987 / 1000000) = -Real.log (1000000 / 1637987) := by
    rw [show ((1637987 / 1000000) : ℝ) = ((1000000 / 1637987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15152_neg : (203215031 / 200000000) ≤ -Real.log (362013 / 1000000) ∧
    -Real.log (362013 / 1000000) ≤ (1016075157 / 1000000000) := by
  have h := checkLog_sound (w := (137987 / 862013)) (n := 12)
    (lo := (12917119 / 40000000)) (hi := (40365997 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362013) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 362013) = 1/(362013 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15152 : Bounds (-1016075157 / 1000000000) (-203215031 / 200000000) (Real.log (362013 / 1000000)) := by
  have h := reflection_log_15152_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15153_neg : (522607107 / 1000000000) ≤ -Real.log (592972587831 / 1000000000000) ∧
    -Real.log (592972587831 / 1000000000000) ≤ (130651777 / 250000000) := by
  have h := checkLog_sound (w := (407027412169 / 1592972587831)) (n := 12)
    (lo := (522607107 / 1000000000)) (hi := (130651777 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 592972587831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 592972587831) = 1/(592972587831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15153 : Bounds (-130651777 / 250000000) (-522607107 / 1000000000) (Real.log (592972587831 / 1000000000000)) := by
  have h := reflection_log_15153_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15154_neg : (25912553 / 50000000) ≤ -Real.log (23822449519 / 40000000000) ∧
    -Real.log (23822449519 / 40000000000) ≤ (518251061 / 1000000000) := by
  have h := checkLog_sound (w := (16177550481 / 63822449519)) (n := 12)
    (lo := (25912553 / 50000000)) (hi := (518251061 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23822449519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23822449519) = 1/(23822449519 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15154 : Bounds (-518251061 / 1000000000) (-25912553 / 50000000) (Real.log (23822449519 / 40000000000)) := by
  have h := reflection_log_15154_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15155_neg : (1502704523 / 1000000000) ≤ -Real.log (25000000000 / 112345657817) ∧
    -Real.log (25000000000 / 112345657817) ≤ (751352263 / 500000000) := by
  have h := checkLog_sound (w := (12345657817 / 212345657817)) (n := 12)
    (lo := (116410163 / 1000000000)) (hi := (29102541 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((112345657817 / 100000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(112345657817 / 100000000000) = 1/(25000000000 / 112345657817) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15155 : Bounds (1502704523 / 1000000000) (751352263 / 500000000) (Real.log (112345657817 / 25000000000)) := by
  have h := reflection_log_15155_neg
  have he : Real.log (112345657817 / 25000000000) = -Real.log (25000000000 / 112345657817) := by
    rw [show ((112345657817 / 25000000000) : ℝ) = ((25000000000 / 112345657817) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15156_neg : (1509543203 / 1000000000) ≤ -Real.log (125000000000 / 565582934867) ∧
    -Real.log (125000000000 / 565582934867) ≤ (754771603 / 500000000) := by
  have h := checkLog_sound (w := (65582934867 / 1065582934867)) (n := 12)
    (lo := (123248843 / 1000000000)) (hi := (30812211 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((565582934867 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(565582934867 / 500000000000) = 1/(125000000000 / 565582934867) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15156 : Bounds (1509543203 / 1000000000) (754771603 / 500000000) (Real.log (565582934867 / 125000000000)) := by
  have h := reflection_log_15156_neg
  have he : Real.log (565582934867 / 125000000000) = -Real.log (125000000000 / 565582934867) := by
    rw [show ((565582934867 / 125000000000) : ℝ) = ((125000000000 / 565582934867) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15157_neg : (4954820511 / 1000000000) ≤ -Real.log (500000000000 / 70928571428571) ∧
    -Real.log (500000000000 / 70928571428571) ≤ (4954820519 / 1000000000) := by
  have h := checkLog_sound (w := (6928571428571 / 134928571428571)) (n := 12)
    (lo := (102790251 / 1000000000)) (hi := (25697563 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((70928571428571 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(70928571428571 / 64000000000000) = 1/(500000000000 / 70928571428571) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15157 : Bounds (4954820511 / 1000000000) (4954820519 / 1000000000) (Real.log (70928571428571 / 500000000000)) := by
  have h := reflection_log_15157_neg
  have he : Real.log (70928571428571 / 500000000000) = -Real.log (500000000000 / 70928571428571) := by
    rw [show ((70928571428571 / 500000000000) : ℝ) = ((500000000000 / 70928571428571) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15158_neg : (5029431881 / 1000000000) ≤ -Real.log (500000000000 / 76423076923077) ∧
    -Real.log (500000000000 / 76423076923077) ≤ (5029431889 / 1000000000) := by
  have h := checkLog_sound (w := (12423076923077 / 140423076923077)) (n := 12)
    (lo := (177401621 / 1000000000)) (hi := (88700811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76423076923077 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(76423076923077 / 64000000000000) = 1/(500000000000 / 76423076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15158 : Bounds (5029431881 / 1000000000) (5029431889 / 1000000000) (Real.log (76423076923077 / 500000000000)) := by
  have h := reflection_log_15158_neg
  have he : Real.log (76423076923077 / 500000000000) = -Real.log (500000000000 / 76423076923077) := by
    rw [show ((76423076923077 / 500000000000) : ℝ) = ((500000000000 / 76423076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15159_neg : (171782277 / 250000000) ≤ -Real.log (250 / 497) ∧
    -Real.log (250 / 497) ≤ (687129109 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 747)) (n := 12)
    (lo := (171782277 / 250000000)) (hi := (687129109 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((497 / 250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(497 / 250) = 1/(250 / 497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15159 : Bounds (171782277 / 250000000) (687129109 / 1000000000) (Real.log (497 / 250)) := by
  have h := reflection_log_15159_neg
  have he : Real.log (497 / 250) = -Real.log (250 / 497) := by
    rw [show ((497 / 250) : ℝ) = ((250 / 497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15160_neg : (35382789 / 8000000) ≤ -Real.log (3 / 250) ∧
    -Real.log (3 / 250) ≤ (552856079 / 125000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 96) = 1/(3 / 250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15160 : Bounds (-552856079 / 125000000) (-35382789 / 8000000) (Real.log (3 / 250)) := by
  have h := reflection_log_15160_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15161_neg : (123439 / 125000000) ≤ -Real.log (250000 / 250247) ∧
    -Real.log (250000 / 250247) ≤ (987513 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 500247)) (n := 12)
    (lo := (123439 / 125000000)) (hi := (987513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250247 / 250000) = 1/(250000 / 250247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15161 : Bounds (123439 / 125000000) (987513 / 1000000000) (Real.log (250247 / 250000)) := by
  have h := reflection_log_15161_neg
  have he : Real.log (250247 / 250000) = -Real.log (250000 / 250247) := by
    rw [show ((250247 / 250000) : ℝ) = ((250000 / 250247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15162_neg : (123561 / 125000000) ≤ -Real.log (249753 / 250000) ∧
    -Real.log (249753 / 250000) ≤ (988489 / 1000000000) := by
  have h := checkLog_sound (w := (247 / 499753)) (n := 12)
    (lo := (123561 / 125000000)) (hi := (988489 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 249753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000 / 249753) = 1/(249753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15162 : Bounds (-988489 / 1000000000) (-123561 / 125000000) (Real.log (249753 / 250000)) := by
  have h := reflection_log_15162_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15163_neg : (493080913 / 1000000000) ≤ -Real.log (1000000 / 1637353) ∧
    -Real.log (1000000 / 1637353) ≤ (246540457 / 500000000) := by
  have h := checkLog_sound (w := (637353 / 2637353)) (n := 12)
    (lo := (493080913 / 1000000000)) (hi := (246540457 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1637353 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1637353 / 1000000) = 1/(1000000 / 1637353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15163 : Bounds (493080913 / 1000000000) (246540457 / 500000000) (Real.log (1637353 / 1000000)) := by
  have h := reflection_log_15163_neg
  have he : Real.log (1637353 / 1000000) = -Real.log (1000000 / 1637353) := by
    rw [show ((1637353 / 1000000) : ℝ) = ((1000000 / 1637353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15164_neg : (1014325369 / 1000000000) ≤ -Real.log (362647 / 1000000) ∧
    -Real.log (362647 / 1000000) ≤ (1014325371 / 1000000000) := by
  have h := checkLog_sound (w := (137353 / 862647)) (n := 12)
    (lo := (321178189 / 1000000000)) (hi := (32117819 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 362647) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 362647) = 1/(362647 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15164 : Bounds (-1014325371 / 1000000000) (-1014325369 / 1000000000) (Real.log (362647 / 1000000)) := by
  have h := reflection_log_15164_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15165_neg : (494331541 / 1000000000) ≤ -Real.log (500000 / 819701) ∧
    -Real.log (500000 / 819701) ≤ (247165771 / 500000000) := by
  have h := checkLog_sound (w := (319701 / 1319701)) (n := 12)
    (lo := (494331541 / 1000000000)) (hi := (247165771 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((819701 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(819701 / 500000) = 1/(500000 / 819701) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15165 : Bounds (494331541 / 1000000000) (247165771 / 500000000) (Real.log (819701 / 500000)) := by
  have h := reflection_log_15165_neg
  have he : Real.log (819701 / 500000) = -Real.log (500000 / 819701) := by
    rw [show ((819701 / 500000) : ℝ) = ((500000 / 819701) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15166_neg : (1019991513 / 1000000000) ≤ -Real.log (180299 / 500000) ∧
    -Real.log (180299 / 500000) ≤ (203998303 / 200000000) := by
  have h := checkLog_sound (w := (69701 / 430299)) (n := 12)
    (lo := (326844333 / 1000000000)) (hi := (163422167 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 180299) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 180299) = 1/(180299 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15166 : Bounds (-203998303 / 200000000) (-1019991513 / 1000000000) (Real.log (180299 / 500000)) := by
  have h := reflection_log_15166_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15167_neg : (525659973 / 1000000000) ≤ -Real.log (147791270599 / 250000000000) ∧
    -Real.log (147791270599 / 250000000000) ≤ (262829987 / 500000000) := by
  have h := checkLog_sound (w := (102208729401 / 397791270599)) (n := 12)
    (lo := (525659973 / 1000000000)) (hi := (262829987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 147791270599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 147791270599) = 1/(147791270599 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15167 : Bounds (-262829987 / 500000000) (-525659973 / 1000000000) (Real.log (147791270599 / 250000000000)) := by
  have h := reflection_log_15167_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0237 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15168_neg : (65155557 / 125000000) ≤ -Real.log (593781153391 / 1000000000000) ∧
    -Real.log (593781153391 / 1000000000000) ≤ (521244457 / 1000000000) := by
  have h := checkLog_sound (w := (406218846609 / 1593781153391)) (n := 12)
    (lo := (65155557 / 125000000)) (hi := (521244457 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 593781153391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 593781153391) = 1/(593781153391 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15168 : Bounds (-521244457 / 1000000000) (-65155557 / 125000000) (Real.log (593781153391 / 1000000000000)) := by
  have h := reflection_log_15168_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15169_neg : (753703141 / 500000000) ≤ -Real.log (250000000000 / 1128751237429) ∧
    -Real.log (250000000000 / 1128751237429) ≤ (301481257 / 200000000) := by
  have h := checkLog_sound (w := (128751237429 / 2128751237429)) (n := 12)
    (lo := (60555961 / 500000000)) (hi := (121111923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1128751237429 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1128751237429 / 1000000000000) = 1/(250000000000 / 1128751237429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15169 : Bounds (753703141 / 500000000) (301481257 / 200000000) (Real.log (1128751237429 / 250000000000)) := by
  have h := reflection_log_15169_neg
  have he : Real.log (1128751237429 / 250000000000) = -Real.log (250000000000 / 1128751237429) := by
    rw [show ((1128751237429 / 250000000000) : ℝ) = ((250000000000 / 1128751237429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15170_neg : (757161527 / 500000000) ≤ -Real.log (500000000000 / 2273171232231) ∧
    -Real.log (500000000000 / 2273171232231) ≤ (1514323057 / 1000000000) := by
  have h := checkLog_sound (w := (273171232231 / 4273171232231)) (n := 12)
    (lo := (64014347 / 500000000)) (hi := (25605739 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2273171232231 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2273171232231 / 2000000000000) = 1/(500000000000 / 2273171232231) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15170 : Bounds (757161527 / 500000000) (1514323057 / 1000000000) (Real.log (2273171232231 / 500000000000)) := by
  have h := reflection_log_15170_neg
  have he : Real.log (2273171232231 / 500000000000) = -Real.log (500000000000 / 2273171232231) := by
    rw [show ((2273171232231 / 500000000000) : ℝ) = ((500000000000 / 2273171232231) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15171_neg : (5029431881 / 1000000000) ≤ -Real.log (125000000000 / 19105769230769) ∧
    -Real.log (125000000000 / 19105769230769) ≤ (5029431889 / 1000000000) := by
  have h := checkLog_sound (w := (3105769230769 / 35105769230769)) (n := 12)
    (lo := (177401621 / 1000000000)) (hi := (88700811 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19105769230769 / 16000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(19105769230769 / 16000000000000) = 1/(125000000000 / 19105769230769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15171 : Bounds (5029431881 / 1000000000) (5029431889 / 1000000000) (Real.log (19105769230769 / 125000000000)) := by
  have h := reflection_log_15171_neg
  have he : Real.log (19105769230769 / 125000000000) = -Real.log (125000000000 / 19105769230769) := by
    rw [show ((19105769230769 / 125000000000) : ℝ) = ((125000000000 / 19105769230769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15172_neg : (5109977733 / 1000000000) ≤ -Real.log (250000000000 / 41416666666667) ∧
    -Real.log (250000000000 / 41416666666667) ≤ (5109977741 / 1000000000) := by
  have h := checkLog_sound (w := (9416666666667 / 73416666666667)) (n := 12)
    (lo := (257947473 / 1000000000)) (hi := (128973737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((41416666666667 / 32000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(41416666666667 / 32000000000000) = 1/(250000000000 / 41416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15172 : Bounds (5109977733 / 1000000000) (5109977741 / 1000000000) (Real.log (41416666666667 / 250000000000)) := by
  have h := reflection_log_15172_neg
  have he : Real.log (41416666666667 / 250000000000) = -Real.log (250000000000 / 41416666666667) := by
    rw [show ((41416666666667 / 250000000000) : ℝ) = ((250000000000 / 41416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15173_neg : (687631999 / 1000000000) ≤ -Real.log (1000 / 1989) ∧
    -Real.log (1000 / 1989) ≤ (42977 / 62500) := by
  have h := checkLog_sound (w := (989 / 2989)) (n := 12)
    (lo := (687631999 / 1000000000)) (hi := (42977 / 62500))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1989 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1989 / 1000) = 1/(1000 / 1989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15173 : Bounds (687631999 / 1000000000) (42977 / 62500) (Real.log (1989 / 1000)) := by
  have h := reflection_log_15173_neg
  have he : Real.log (1989 / 1000) = -Real.log (1000 / 1989) := by
    rw [show ((1989 / 1000) : ℝ) = ((1000 / 1989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15174_neg : (2254930001 / 500000000) ≤ -Real.log (11 / 1000) ∧
    -Real.log (11 / 1000) ≤ (4509860009 / 1000000000) := by
  have h := checkLog_sound (w := (37 / 213)) (n := 12)
    (lo := (175488461 / 500000000)) (hi := (350976923 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 88) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(125 / 88) = 1/(11 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15174 : Bounds (-4509860009 / 1000000000) (-2254930001 / 500000000) (Real.log (11 / 1000)) := by
  have h := reflection_log_15174_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15175_neg : (988511 / 1000000000) ≤ -Real.log (1000000 / 1000989) ∧
    -Real.log (1000000 / 1000989) ≤ (30891 / 31250000) := by
  have h := checkLog_sound (w := (989 / 2000989)) (n := 12)
    (lo := (988511 / 1000000000)) (hi := (30891 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000989 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000989 / 1000000) = 1/(1000000 / 1000989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15175 : Bounds (988511 / 1000000000) (30891 / 31250000) (Real.log (1000989 / 1000000)) := by
  have h := reflection_log_15175_neg
  have he : Real.log (1000989 / 1000000) = -Real.log (1000000 / 1000989) := by
    rw [show ((1000989 / 1000000) : ℝ) = ((1000000 / 1000989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15176_neg : (989489 / 1000000000) ≤ -Real.log (999011 / 1000000) ∧
    -Real.log (999011 / 1000000) ≤ (98949 / 100000000) := by
  have h := checkLog_sound (w := (989 / 1999011)) (n := 12)
    (lo := (989489 / 1000000000)) (hi := (98949 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999011) = 1/(999011 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15176 : Bounds (-98949 / 100000000) (-989489 / 1000000000) (Real.log (999011 / 1000000)) := by
  have h := reflection_log_15176_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15177_neg : (9878907 / 20000000) ≤ -Real.log (1000000 / 1638769) ∧
    -Real.log (1000000 / 1638769) ≤ (493945351 / 1000000000) := by
  have h := checkLog_sound (w := (638769 / 2638769)) (n := 12)
    (lo := (9878907 / 20000000)) (hi := (493945351 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1638769 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1638769 / 1000000) = 1/(1000000 / 1638769) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15177 : Bounds (9878907 / 20000000) (493945351 / 1000000000) (Real.log (1638769 / 1000000)) := by
  have h := reflection_log_15177_neg
  have he : Real.log (1638769 / 1000000) = -Real.log (1000000 / 1638769) := by
    rw [show ((1638769 / 1000000) : ℝ) = ((1000000 / 1638769) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15178_neg : (203647527 / 200000000) ≤ -Real.log (361231 / 1000000) ∧
    -Real.log (361231 / 1000000) ≤ (1018237637 / 1000000000) := by
  have h := checkLog_sound (w := (138769 / 861231)) (n := 12)
    (lo := (65018091 / 200000000)) (hi := (40636307 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 361231) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 361231) = 1/(361231 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15178 : Bounds (-1018237637 / 1000000000) (-203647527 / 200000000) (Real.log (361231 / 1000000)) := by
  have h := reflection_log_15178_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15179_neg : (123801467 / 250000000) ≤ -Real.log (250000 / 410209) ∧
    -Real.log (250000 / 410209) ≤ (495205869 / 1000000000) := by
  have h := checkLog_sound (w := (160209 / 660209)) (n := 12)
    (lo := (123801467 / 250000000)) (hi := (495205869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((410209 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(410209 / 250000) = 1/(250000 / 410209) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15179 : Bounds (123801467 / 250000000) (495205869 / 1000000000) (Real.log (410209 / 250000)) := by
  have h := reflection_log_15179_neg
  have he : Real.log (410209 / 250000) = -Real.log (250000 / 410209) := by
    rw [show ((410209 / 250000) : ℝ) = ((250000 / 410209) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15180_neg : (1023976169 / 1000000000) ≤ -Real.log (89791 / 250000) ∧
    -Real.log (89791 / 250000) ≤ (1023976171 / 1000000000) := by
  have h := checkLog_sound (w := (35209 / 214791)) (n := 12)
    (lo := (330828989 / 1000000000)) (hi := (33082899 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 89791) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 89791) = 1/(89791 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15180 : Bounds (-1023976171 / 1000000000) (-1023976169 / 1000000000) (Real.log (89791 / 250000)) := by
  have h := reflection_log_15180_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15181_neg : (264385151 / 500000000) ≤ -Real.log (36833076319 / 62500000000) ∧
    -Real.log (36833076319 / 62500000000) ≤ (528770303 / 1000000000) := by
  have h := checkLog_sound (w := (25666923681 / 99333076319)) (n := 12)
    (lo := (264385151 / 500000000)) (hi := (528770303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36833076319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36833076319) = 1/(36833076319 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15181 : Bounds (-528770303 / 1000000000) (-264385151 / 500000000) (Real.log (36833076319 / 62500000000)) := by
  have h := reflection_log_15181_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15182_neg : (104858457 / 200000000) ≤ -Real.log (591974164639 / 1000000000000) ∧
    -Real.log (591974164639 / 1000000000000) ≤ (262146143 / 500000000) := by
  have h := checkLog_sound (w := (408025835361 / 1591974164639)) (n := 12)
    (lo := (104858457 / 200000000)) (hi := (262146143 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 591974164639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 591974164639) = 1/(591974164639 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15182 : Bounds (-262146143 / 500000000) (-104858457 / 200000000) (Real.log (591974164639 / 1000000000000)) := by
  have h := reflection_log_15182_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15183_neg : (302436597 / 200000000) ≤ -Real.log (500000000000 / 2268311689749) ∧
    -Real.log (500000000000 / 2268311689749) ≤ (378045747 / 250000000) := by
  have h := checkLog_sound (w := (268311689749 / 4268311689749)) (n := 12)
    (lo := (1007109 / 8000000)) (hi := (62944313 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2268311689749 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2268311689749 / 2000000000000) = 1/(500000000000 / 2268311689749) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15183 : Bounds (302436597 / 200000000) (378045747 / 250000000) (Real.log (2268311689749 / 500000000000)) := by
  have h := reflection_log_15183_neg
  have he : Real.log (2268311689749 / 500000000000) = -Real.log (500000000000 / 2268311689749) := by
    rw [show ((2268311689749 / 500000000000) : ℝ) = ((500000000000 / 2268311689749) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15184_neg : (1519182037 / 1000000000) ≤ -Real.log (15625000000 / 71382606553) ∧
    -Real.log (15625000000 / 71382606553) ≤ (37979551 / 25000000) := by
  have h := checkLog_sound (w := (8882606553 / 133882606553)) (n := 12)
    (lo := (132887677 / 1000000000)) (hi := (66443839 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71382606553 / 62500000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(71382606553 / 62500000000) = 1/(15625000000 / 71382606553) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15184 : Bounds (1519182037 / 1000000000) (37979551 / 25000000) (Real.log (71382606553 / 15625000000)) := by
  have h := reflection_log_15184_neg
  have he : Real.log (71382606553 / 15625000000) = -Real.log (15625000000 / 71382606553) := by
    rw [show ((71382606553 / 15625000000) : ℝ) = ((15625000000 / 71382606553) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15185_neg : (5109977733 / 1000000000) ≤ -Real.log (500000000000 / 82833333333333) ∧
    -Real.log (500000000000 / 82833333333333) ≤ (5109977741 / 1000000000) := by
  have h := checkLog_sound (w := (18833333333333 / 146833333333333)) (n := 12)
    (lo := (257947473 / 1000000000)) (hi := (128973737 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((82833333333333 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(82833333333333 / 64000000000000) = 1/(500000000000 / 82833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15185 : Bounds (5109977733 / 1000000000) (5109977741 / 1000000000) (Real.log (82833333333333 / 500000000000)) := by
  have h := reflection_log_15185_neg
  have he : Real.log (82833333333333 / 500000000000) = -Real.log (500000000000 / 82833333333333) := by
    rw [show ((82833333333333 / 500000000000) : ℝ) = ((500000000000 / 82833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15186_neg : (2598746001 / 500000000) ≤ -Real.log (500000000000 / 90409090909091) ∧
    -Real.log (500000000000 / 90409090909091) ≤ (519749201 / 100000000) := by
  have h := checkLog_sound (w := (26409090909091 / 154409090909091)) (n := 12)
    (lo := (172730871 / 500000000)) (hi := (345461743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90409090909091 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(90409090909091 / 64000000000000) = 1/(500000000000 / 90409090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15186 : Bounds (2598746001 / 500000000) (519749201 / 100000000) (Real.log (90409090909091 / 500000000000)) := by
  have h := reflection_log_15186_neg
  have he : Real.log (90409090909091 / 500000000000) = -Real.log (500000000000 / 90409090909091) := by
    rw [show ((90409090909091 / 500000000000) : ℝ) = ((500000000000 / 90409090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15187_neg : (344067319 / 500000000) ≤ -Real.log (100 / 199) ∧
    -Real.log (100 / 199) ≤ (688134639 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 299)) (n := 12)
    (lo := (344067319 / 500000000)) (hi := (688134639 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 100) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(199 / 100) = 1/(100 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15187 : Bounds (344067319 / 500000000) (688134639 / 1000000000) (Real.log (199 / 100)) := by
  have h := reflection_log_15187_neg
  have he : Real.log (199 / 100) = -Real.log (100 / 199) := by
    rw [show ((199 / 100) : ℝ) = ((100 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15188_neg : (2302585091 / 500000000) ≤ -Real.log (1 / 100) ∧
    -Real.log (1 / 100) ≤ (4605170189 / 1000000000) := by
  have h := checkLog_sound (w := (9 / 41)) (n := 12)
    (lo := (223143551 / 500000000)) (hi := (446287103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((25 / 16) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(25 / 16) = 1/(1 / 100) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15188 : Bounds (-4605170189 / 1000000000) (-2302585091 / 500000000) (Real.log (1 / 100)) := by
  have h := reflection_log_15188_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15189_neg : (98951 / 100000000) ≤ -Real.log (100000 / 100099) ∧
    -Real.log (100000 / 100099) ≤ (989511 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 200099)) (n := 12)
    (lo := (98951 / 100000000)) (hi := (989511 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100099 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100099 / 100000) = 1/(100000 / 100099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15189 : Bounds (98951 / 100000000) (989511 / 1000000000) (Real.log (100099 / 100000)) := by
  have h := reflection_log_15189_neg
  have he : Real.log (100099 / 100000) = -Real.log (100000 / 100099) := by
    rw [show ((100099 / 100000) : ℝ) = ((100000 / 100099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15190_neg : (99049 / 100000000) ≤ -Real.log (99901 / 100000) ∧
    -Real.log (99901 / 100000) ≤ (990491 / 1000000000) := by
  have h := checkLog_sound (w := (99 / 199901)) (n := 12)
    (lo := (99049 / 100000000)) (hi := (990491 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 99901) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 99901) = 1/(99901 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15190 : Bounds (-990491 / 1000000000) (-99049 / 100000000) (Real.log (99901 / 100000)) := by
  have h := reflection_log_15190_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15191_neg : (247410617 / 500000000) ≤ -Real.log (200000 / 328041) ∧
    -Real.log (200000 / 328041) ≤ (98964247 / 200000000) := by
  have h := checkLog_sound (w := (128041 / 528041)) (n := 12)
    (lo := (247410617 / 500000000)) (hi := (98964247 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328041 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328041 / 200000) = 1/(200000 / 328041) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15191 : Bounds (247410617 / 500000000) (98964247 / 200000000) (Real.log (328041 / 200000)) := by
  have h := reflection_log_15191_neg
  have he : Real.log (328041 / 200000) = -Real.log (200000 / 328041) := by
    rw [show ((328041 / 200000) : ℝ) = ((200000 / 328041) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15192_neg : (1022220853 / 1000000000) ≤ -Real.log (71959 / 200000) ∧
    -Real.log (71959 / 200000) ≤ (204444171 / 200000000) := by
  have h := checkLog_sound (w := (28041 / 171959)) (n := 12)
    (lo := (329073673 / 1000000000)) (hi := (164536837 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71959) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71959) = 1/(71959 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15192 : Bounds (-204444171 / 200000000) (-1022220853 / 1000000000) (Real.log (71959 / 200000)) := by
  have h := reflection_log_15192_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15193_neg : (248046109 / 500000000) ≤ -Real.log (1000000 / 1642291) ∧
    -Real.log (1000000 / 1642291) ≤ (496092219 / 1000000000) := by
  have h := checkLog_sound (w := (642291 / 2642291)) (n := 12)
    (lo := (248046109 / 500000000)) (hi := (496092219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1642291 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1642291 / 1000000) = 1/(1000000 / 1642291) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15193 : Bounds (248046109 / 500000000) (496092219 / 1000000000) (Real.log (1642291 / 1000000)) := by
  have h := reflection_log_15193_neg
  have he : Real.log (1642291 / 1000000) = -Real.log (1000000 / 1642291) := by
    rw [show ((1642291 / 1000000) : ℝ) = ((1000000 / 1642291) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15194_neg : (1028035471 / 1000000000) ≤ -Real.log (357709 / 1000000) ∧
    -Real.log (357709 / 1000000) ≤ (1028035473 / 1000000000) := by
  have h := checkLog_sound (w := (142291 / 857709)) (n := 12)
    (lo := (334888291 / 1000000000)) (hi := (83722073 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 357709) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 357709) = 1/(357709 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15194 : Bounds (-1028035473 / 1000000000) (-1028035471 / 1000000000) (Real.log (357709 / 1000000)) := by
  have h := reflection_log_15194_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15195_neg : (265971627 / 500000000) ≤ -Real.log (587462271319 / 1000000000000) ∧
    -Real.log (587462271319 / 1000000000000) ≤ (106388651 / 200000000) := by
  have h := checkLog_sound (w := (412537728681 / 1587462271319)) (n := 12)
    (lo := (265971627 / 500000000)) (hi := (106388651 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 587462271319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 587462271319) = 1/(587462271319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15195 : Bounds (-106388651 / 200000000) (-265971627 / 500000000) (Real.log (587462271319 / 1000000000000)) := by
  have h := reflection_log_15195_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15196_neg : (26369981 / 50000000) ≤ -Real.log (23605502319 / 40000000000) ∧
    -Real.log (23605502319 / 40000000000) ≤ (527399621 / 1000000000) := by
  have h := checkLog_sound (w := (16394497681 / 63605502319)) (n := 12)
    (lo := (26369981 / 50000000)) (hi := (527399621 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23605502319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23605502319) = 1/(23605502319 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15196 : Bounds (-527399621 / 1000000000) (-26369981 / 50000000) (Real.log (23605502319 / 40000000000)) := by
  have h := reflection_log_15196_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15197_neg : (1517042087 / 1000000000) ≤ -Real.log (125000000000 / 569840117289) ∧
    -Real.log (125000000000 / 569840117289) ≤ (151704209 / 100000000) := by
  have h := checkLog_sound (w := (69840117289 / 1069840117289)) (n := 12)
    (lo := (130747727 / 1000000000)) (hi := (8171733 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((569840117289 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(569840117289 / 500000000000) = 1/(125000000000 / 569840117289) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15197 : Bounds (1517042087 / 1000000000) (151704209 / 100000000) (Real.log (569840117289 / 125000000000)) := by
  have h := reflection_log_15197_neg
  have he : Real.log (569840117289 / 125000000000) = -Real.log (125000000000 / 569840117289) := by
    rw [show ((569840117289 / 125000000000) : ℝ) = ((125000000000 / 569840117289) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15198_neg : (1524127689 / 1000000000) ≤ -Real.log (50000000000 / 229556846487) ∧
    -Real.log (50000000000 / 229556846487) ≤ (381031923 / 250000000) := by
  have h := checkLog_sound (w := (29556846487 / 429556846487)) (n := 12)
    (lo := (137833329 / 1000000000)) (hi := (13783333 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((229556846487 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(229556846487 / 200000000000) = 1/(50000000000 / 229556846487) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15198 : Bounds (1524127689 / 1000000000) (381031923 / 250000000) (Real.log (229556846487 / 50000000000)) := by
  have h := reflection_log_15198_neg
  have he : Real.log (229556846487 / 50000000000) = -Real.log (50000000000 / 229556846487) := by
    rw [show ((229556846487 / 50000000000) : ℝ) = ((50000000000 / 229556846487) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15199_neg : (2598746001 / 500000000) ≤ -Real.log (50000000000 / 9040909090909) ∧
    -Real.log (50000000000 / 9040909090909) ≤ (519749201 / 100000000) := by
  have h := checkLog_sound (w := (2640909090909 / 15440909090909)) (n := 12)
    (lo := (172730871 / 500000000)) (hi := (345461743 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9040909090909 / 6400000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(9040909090909 / 6400000000000) = 1/(50000000000 / 9040909090909) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15199 : Bounds (2598746001 / 500000000) (519749201 / 100000000) (Real.log (9040909090909 / 50000000000)) := by
  have h := reflection_log_15199_neg
  have he : Real.log (9040909090909 / 50000000000) = -Real.log (50000000000 / 9040909090909) := by
    rw [show ((9040909090909 / 50000000000) : ℝ) = ((50000000000 / 9040909090909) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15200_neg : (264665241 / 50000000) ≤ -Real.log (1 / 199) ∧
    -Real.log (1 / 199) ≤ (1323326207 / 250000000) := by
  have h := checkLog_sound (w := (71 / 327)) (n := 12)
    (lo := (1378983 / 3125000)) (hi := (441274561 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((199 / 128) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(199 / 128) = 1/(1 / 199) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15200 : Bounds (264665241 / 50000000) (1323326207 / 250000000) (Real.log (199 / 1)) := by
  have h := reflection_log_15200_neg
  have he : Real.log (199 / 1) = -Real.log (1 / 199) := by
    rw [show ((199 / 1) : ℝ) = ((1 / 199) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15201_neg : (5376837 / 7812500) ≤ -Real.log (5000 / 9951) ∧
    -Real.log (5000 / 9951) ≤ (688235137 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 14951)) (n := 12)
    (lo := (5376837 / 7812500)) (hi := (688235137 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9951 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9951 / 5000) = 1/(5000 / 9951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15201 : Bounds (5376837 / 7812500) (688235137 / 1000000000) (Real.log (9951 / 5000)) := by
  have h := reflection_log_15201_neg
  have he : Real.log (9951 / 5000) = -Real.log (5000 / 9951) := by
    rw [show ((9951 / 5000) : ℝ) = ((5000 / 9951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15202_neg : (4625372889 / 1000000000) ≤ -Real.log (49 / 5000) ∧
    -Real.log (49 / 5000) ≤ (144542903 / 31250000) := by
  have h := checkLog_sound (w := (233 / 1017)) (n := 12)
    (lo := (466489809 / 1000000000)) (hi := (46648981 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 392) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 392) = 1/(49 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15202 : Bounds (-144542903 / 31250000) (-4625372889 / 1000000000) (Real.log (49 / 5000)) := by
  have h := reflection_log_15202_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15203_neg : (98971 / 100000000) ≤ -Real.log (5000000 / 5004951) ∧
    -Real.log (5000000 / 5004951) ≤ (989711 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 10004951)) (n := 12)
    (lo := (98971 / 100000000)) (hi := (989711 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004951 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004951 / 5000000) = 1/(5000000 / 5004951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15203 : Bounds (98971 / 100000000) (989711 / 1000000000) (Real.log (5004951 / 5000000)) := by
  have h := reflection_log_15203_neg
  have he : Real.log (5004951 / 5000000) = -Real.log (5000000 / 5004951) := by
    rw [show ((5004951 / 5000000) : ℝ) = ((5000000 / 5004951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15204_neg : (99069 / 100000000) ≤ -Real.log (4995049 / 5000000) ∧
    -Real.log (4995049 / 5000000) ≤ (990691 / 1000000000) := by
  have h := checkLog_sound (w := (4951 / 9995049)) (n := 12)
    (lo := (99069 / 100000000)) (hi := (990691 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995049) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995049) = 1/(4995049 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15204 : Bounds (-990691 / 1000000000) (-99069 / 100000000) (Real.log (4995049 / 5000000)) := by
  have h := reflection_log_15204_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15205_neg : (247854267 / 500000000) ≤ -Real.log (1000000 / 1641661) ∧
    -Real.log (1000000 / 1641661) ≤ (99141707 / 200000000) := by
  have h := checkLog_sound (w := (641661 / 2641661)) (n := 12)
    (lo := (247854267 / 500000000)) (hi := (99141707 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1641661 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1641661 / 1000000) = 1/(1000000 / 1641661) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15205 : Bounds (247854267 / 500000000) (99141707 / 200000000) (Real.log (1641661 / 1000000)) := by
  have h := reflection_log_15205_neg
  have he : Real.log (1641661 / 1000000) = -Real.log (1000000 / 1641661) := by
    rw [show ((1641661 / 1000000) : ℝ) = ((1000000 / 1641661) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15206_neg : (256568953 / 250000000) ≤ -Real.log (358339 / 1000000) ∧
    -Real.log (358339 / 1000000) ≤ (513137907 / 500000000) := by
  have h := checkLog_sound (w := (141661 / 858339)) (n := 12)
    (lo := (41641079 / 125000000)) (hi := (333128633 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 358339) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 358339) = 1/(358339 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15206 : Bounds (-513137907 / 500000000) (-256568953 / 250000000) (Real.log (358339 / 1000000)) := by
  have h := reflection_log_15206_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15207_neg : (24813561 / 50000000) ≤ -Real.log (200000 / 328517) ∧
    -Real.log (200000 / 328517) ≤ (496271221 / 1000000000) := by
  have h := checkLog_sound (w := (128517 / 528517)) (n := 12)
    (lo := (24813561 / 50000000)) (hi := (496271221 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328517 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328517 / 200000) = 1/(200000 / 328517) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15207 : Bounds (24813561 / 50000000) (496271221 / 1000000000) (Real.log (328517 / 200000)) := by
  have h := reflection_log_15207_neg
  have he : Real.log (328517 / 200000) = -Real.log (200000 / 328517) := by
    rw [show ((328517 / 200000) : ℝ) = ((200000 / 328517) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15208_neg : (514428853 / 500000000) ≤ -Real.log (71483 / 200000) ∧
    -Real.log (71483 / 200000) ≤ (257214427 / 250000000) := by
  have h := checkLog_sound (w := (28517 / 171483)) (n := 12)
    (lo := (167855263 / 500000000)) (hi := (335710527 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71483) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71483) = 1/(71483 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15208 : Bounds (-257214427 / 250000000) (-514428853 / 500000000) (Real.log (71483 / 200000)) := by
  have h := reflection_log_15208_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15209_neg : (266293243 / 500000000) ≤ -Real.log (23483380711 / 40000000000) ∧
    -Real.log (23483380711 / 40000000000) ≤ (532586487 / 1000000000) := by
  have h := checkLog_sound (w := (16516619289 / 63483380711)) (n := 12)
    (lo := (266293243 / 500000000)) (hi := (532586487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23483380711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23483380711) = 1/(23483380711 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15209 : Bounds (-532586487 / 1000000000) (-266293243 / 500000000) (Real.log (23483380711 / 40000000000)) := by
  have h := reflection_log_15209_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15210_neg : (530567279 / 1000000000) ≤ -Real.log (588271161079 / 1000000000000) ∧
    -Real.log (588271161079 / 1000000000000) ≤ (6632091 / 12500000) := by
  have h := checkLog_sound (w := (411728838921 / 1588271161079)) (n := 12)
    (lo := (530567279 / 1000000000)) (hi := (6632091 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 588271161079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 588271161079) = 1/(588271161079 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15210 : Bounds (-6632091 / 12500000) (-530567279 / 1000000000) (Real.log (588271161079 / 1000000000000)) := by
  have h := reflection_log_15210_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15211_neg : (760992173 / 500000000) ≤ -Real.log (500000000000 / 2290653543153) ∧
    -Real.log (500000000000 / 2290653543153) ≤ (1521984349 / 1000000000) := by
  have h := checkLog_sound (w := (290653543153 / 4290653543153)) (n := 12)
    (lo := (67844993 / 500000000)) (hi := (135689987 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2290653543153 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2290653543153 / 2000000000000) = 1/(500000000000 / 2290653543153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15211 : Bounds (760992173 / 500000000) (1521984349 / 1000000000) (Real.log (2290653543153 / 500000000000)) := by
  have h := reflection_log_15211_neg
  have he : Real.log (2290653543153 / 500000000000) = -Real.log (500000000000 / 2290653543153) := by
    rw [show ((2290653543153 / 500000000000) : ℝ) = ((500000000000 / 2290653543153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15212_neg : (762564463 / 500000000) ≤ -Real.log (250000000000 / 1148934012283) ∧
    -Real.log (250000000000 / 1148934012283) ≤ (1525128929 / 1000000000) := by
  have h := checkLog_sound (w := (148934012283 / 2148934012283)) (n := 12)
    (lo := (69417283 / 500000000)) (hi := (138834567 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1148934012283 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1148934012283 / 1000000000000) = 1/(250000000000 / 1148934012283) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15212 : Bounds (762564463 / 500000000) (1525128929 / 1000000000) (Real.log (1148934012283 / 250000000000)) := by
  have h := reflection_log_15212_neg
  have he : Real.log (1148934012283 / 250000000000) = -Real.log (250000000000 / 1148934012283) := by
    rw [show ((1148934012283 / 250000000000) : ℝ) = ((250000000000 / 1148934012283) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15213_neg : (212544321 / 40000000) ≤ -Real.log (500000000000 / 101540816326531) ∧
    -Real.log (500000000000 / 101540816326531) ≤ (5313608033 / 1000000000) := by
  have h := checkLog_sound (w := (37540816326531 / 165540816326531)) (n := 12)
    (lo := (92315553 / 200000000)) (hi := (230788883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((101540816326531 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(101540816326531 / 64000000000000) = 1/(500000000000 / 101540816326531) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15213 : Bounds (212544321 / 40000000) (5313608033 / 1000000000) (Real.log (101540816326531 / 500000000000)) := by
  have h := reflection_log_15213_neg
  have he : Real.log (101540816326531 / 500000000000) = -Real.log (500000000000 / 101540816326531) := by
    rw [show ((101540816326531 / 500000000000) : ℝ) = ((500000000000 / 101540816326531) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15214_neg : (688335623 / 1000000000) ≤ -Real.log (625 / 1244) ∧
    -Real.log (625 / 1244) ≤ (86041953 / 125000000) := by
  have h := checkLog_sound (w := (619 / 1869)) (n := 12)
    (lo := (688335623 / 1000000000)) (hi := (86041953 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1244 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1244 / 625) = 1/(625 / 1244) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15214 : Bounds (688335623 / 1000000000) (86041953 / 125000000) (Real.log (1244 / 625)) := by
  have h := reflection_log_15214_neg
  have he : Real.log (1244 / 625) = -Real.log (625 / 1244) := by
    rw [show ((1244 / 625) : ℝ) = ((625 / 1244) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15215_neg : (4645992177 / 1000000000) ≤ -Real.log (6 / 625) ∧
    -Real.log (6 / 625) ≤ (580749023 / 125000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 384) = 1/(6 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15215 : Bounds (-580749023 / 125000000) (-4645992177 / 1000000000) (Real.log (6 / 625)) := by
  have h := reflection_log_15215_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15216_neg : (989909 / 1000000000) ≤ -Real.log (625000 / 625619) ∧
    -Real.log (625000 / 625619) ≤ (98991 / 100000000) := by
  have h := checkLog_sound (w := (619 / 1250619)) (n := 12)
    (lo := (989909 / 1000000000)) (hi := (98991 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625619 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625619 / 625000) = 1/(625000 / 625619) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15216 : Bounds (989909 / 1000000000) (98991 / 100000000) (Real.log (625619 / 625000)) := by
  have h := reflection_log_15216_neg
  have he : Real.log (625619 / 625000) = -Real.log (625000 / 625619) := by
    rw [show ((625619 / 625000) : ℝ) = ((625000 / 625619) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15217_neg : (99089 / 100000000) ≤ -Real.log (624381 / 625000) ∧
    -Real.log (624381 / 625000) ≤ (990891 / 1000000000) := by
  have h := checkLog_sound (w := (619 / 1249381)) (n := 12)
    (lo := (99089 / 100000000)) (hi := (990891 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624381) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624381) = 1/(624381 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15217 : Bounds (-990891 / 1000000000) (-99089 / 100000000) (Real.log (624381 / 625000)) := by
  have h := reflection_log_15217_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15218_neg : (99177521 / 200000000) ≤ -Real.log (200000 / 328391) ∧
    -Real.log (200000 / 328391) ≤ (247943803 / 500000000) := by
  have h := checkLog_sound (w := (128391 / 528391)) (n := 12)
    (lo := (99177521 / 200000000)) (hi := (247943803 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((328391 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(328391 / 200000) = 1/(200000 / 328391) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15218 : Bounds (99177521 / 200000000) (247943803 / 500000000) (Real.log (328391 / 200000)) := by
  have h := reflection_log_15218_neg
  have he : Real.log (328391 / 200000) = -Real.log (200000 / 328391) := by
    rw [show ((328391 / 200000) : ℝ) = ((200000 / 328391) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15219_neg : (1027096601 / 1000000000) ≤ -Real.log (71609 / 200000) ∧
    -Real.log (71609 / 200000) ≤ (1027096603 / 1000000000) := by
  have h := checkLog_sound (w := (28391 / 171609)) (n := 12)
    (lo := (333949421 / 1000000000)) (hi := (166974711 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 71609) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 71609) = 1/(71609 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15219 : Bounds (-1027096603 / 1000000000) (-1027096601 / 1000000000) (Real.log (71609 / 200000)) := by
  have h := reflection_log_15219_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15220_neg : (496450799 / 1000000000) ≤ -Real.log (3125 / 5134) ∧
    -Real.log (3125 / 5134) ≤ (1241127 / 2500000) := by
  have h := checkLog_sound (w := (2009 / 8259)) (n := 12)
    (lo := (496450799 / 1000000000)) (hi := (1241127 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5134 / 3125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5134 / 3125) = 1/(3125 / 5134) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15220 : Bounds (496450799 / 1000000000) (1241127 / 2500000) (Real.log (5134 / 3125)) := by
  have h := reflection_log_15220_neg
  have he : Real.log (5134 / 3125) = -Real.log (3125 / 5134) := by
    rw [show ((5134 / 3125) : ℝ) = ((3125 / 5134) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15221_neg : (514841709 / 500000000) ≤ -Real.log (1116 / 3125) ∧
    -Real.log (1116 / 3125) ≤ (51484171 / 50000000) := by
  have h := checkLog_sound (w := (893 / 5357)) (n := 12)
    (lo := (168268119 / 500000000)) (hi := (336536239 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2232) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2232) = 1/(1116 / 3125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15221 : Bounds (-51484171 / 50000000) (-514841709 / 500000000) (Real.log (1116 / 3125)) := by
  have h := reflection_log_15221_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15222_neg : (533232619 / 1000000000) ≤ -Real.log (5729544 / 9765625) ∧
    -Real.log (5729544 / 9765625) ≤ (26661631 / 50000000) := by
  have h := checkLog_sound (w := (4036081 / 15495169)) (n := 12)
    (lo := (533232619 / 1000000000)) (hi := (26661631 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9765625 / 5729544) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9765625 / 5729544) = 1/(5729544 / 9765625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15222 : Bounds (-26661631 / 50000000) (-533232619 / 1000000000) (Real.log (5729544 / 9765625)) := by
  have h := reflection_log_15222_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15223_neg : (531208997 / 1000000000) ≤ -Real.log (23515751119 / 40000000000) ∧
    -Real.log (23515751119 / 40000000000) ≤ (265604499 / 500000000) := by
  have h := checkLog_sound (w := (16484248881 / 63515751119)) (n := 12)
    (lo := (531208997 / 1000000000)) (hi := (265604499 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 23515751119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 23515751119) = 1/(23515751119 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15223 : Bounds (-265604499 / 500000000) (-531208997 / 1000000000) (Real.log (23515751119 / 40000000000)) := by
  have h := reflection_log_15223_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15224_neg : (761492103 / 500000000) ≤ -Real.log (500000000000 / 2292945020877) ∧
    -Real.log (500000000000 / 2292945020877) ≤ (1522984209 / 1000000000) := by
  have h := checkLog_sound (w := (292945020877 / 4292945020877)) (n := 12)
    (lo := (68344923 / 500000000)) (hi := (136689847 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2292945020877 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2292945020877 / 2000000000000) = 1/(500000000000 / 2292945020877) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15224 : Bounds (761492103 / 500000000) (1522984209 / 1000000000) (Real.log (2292945020877 / 500000000000)) := by
  have h := reflection_log_15224_neg
  have he : Real.log (2292945020877 / 500000000000) = -Real.log (500000000000 / 2292945020877) := by
    rw [show ((2292945020877 / 500000000000) : ℝ) = ((500000000000 / 2292945020877) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15225_neg : (1526134217 / 1000000000) ≤ -Real.log (50000000000 / 230017921147) ∧
    -Real.log (50000000000 / 230017921147) ≤ (76306711 / 50000000) := by
  have h := checkLog_sound (w := (30017921147 / 430017921147)) (n := 12)
    (lo := (139839857 / 1000000000)) (hi := (69919929 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((230017921147 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(230017921147 / 200000000000) = 1/(50000000000 / 230017921147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15225 : Bounds (1526134217 / 1000000000) (76306711 / 50000000) (Real.log (230017921147 / 50000000000)) := by
  have h := reflection_log_15225_neg
  have he : Real.log (230017921147 / 50000000000) = -Real.log (50000000000 / 230017921147) := by
    rw [show ((230017921147 / 50000000000) : ℝ) = ((50000000000 / 230017921147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15226_neg : (212544321 / 40000000) ≤ -Real.log (50000000000 / 10154081632653) ∧
    -Real.log (50000000000 / 10154081632653) ≤ (5313608033 / 1000000000) := by
  have h := checkLog_sound (w := (3754081632653 / 16554081632653)) (n := 12)
    (lo := (92315553 / 200000000)) (hi := (230788883 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10154081632653 / 6400000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(10154081632653 / 6400000000000) = 1/(50000000000 / 10154081632653) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15226 : Bounds (212544321 / 40000000) (5313608033 / 1000000000) (Real.log (10154081632653 / 50000000000)) := by
  have h := reflection_log_15226_neg
  have he : Real.log (10154081632653 / 50000000000) = -Real.log (50000000000 / 10154081632653) := by
    rw [show ((10154081632653 / 50000000000) : ℝ) = ((50000000000 / 10154081632653) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15227_neg : (26671639 / 5000000) ≤ -Real.log (500000000000 / 103666666666667) ∧
    -Real.log (500000000000 / 103666666666667) ≤ (10418609 / 1953125) := by
  have h := checkLog_sound (w := (39666666666667 / 167666666666667)) (n := 12)
    (lo := (24114877 / 50000000)) (hi := (482297541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((103666666666667 / 64000000000000) : ℝ) 7 (by norm_num)
  have hq : (2 : ℝ)^7*(103666666666667 / 64000000000000) = 1/(500000000000 / 103666666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15227 : Bounds (26671639 / 5000000) (10418609 / 1953125) (Real.log (103666666666667 / 500000000000)) := by
  have h := reflection_log_15227_neg
  have he : Real.log (103666666666667 / 500000000000) = -Real.log (500000000000 / 103666666666667) := by
    rw [show ((103666666666667 / 500000000000) : ℝ) = ((500000000000 / 103666666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15228_neg : (6884361 / 10000000) ≤ -Real.log (5000 / 9953) ∧
    -Real.log (5000 / 9953) ≤ (688436101 / 1000000000) := by
  have h := checkLog_sound (w := (4953 / 14953)) (n := 12)
    (lo := (6884361 / 10000000)) (hi := (688436101 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9953 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9953 / 5000) = 1/(5000 / 9953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15228 : Bounds (6884361 / 10000000) (688436101 / 1000000000) (Real.log (9953 / 5000)) := by
  have h := reflection_log_15228_neg
  have he : Real.log (9953 / 5000) = -Real.log (5000 / 9953) := by
    rw [show ((9953 / 5000) : ℝ) = ((5000 / 9953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15229_neg : (2333522793 / 500000000) ≤ -Real.log (47 / 5000) ∧
    -Real.log (47 / 5000) ≤ (4667045593 / 1000000000) := by
  have h := checkLog_sound (w := (249 / 1001)) (n := 12)
    (lo := (254081253 / 500000000)) (hi := (508162507 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 376) : ℝ) 6 (by norm_num)
  have hq : (2 : ℝ)^6*(625 / 376) = 1/(47 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15229 : Bounds (-4667045593 / 1000000000) (-2333522793 / 500000000) (Real.log (47 / 5000)) := by
  have h := reflection_log_15229_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15230_neg : (990109 / 1000000000) ≤ -Real.log (5000000 / 5004953) ∧
    -Real.log (5000000 / 5004953) ≤ (99011 / 100000000) := by
  have h := checkLog_sound (w := (4953 / 10004953)) (n := 12)
    (lo := (990109 / 1000000000)) (hi := (99011 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004953 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004953 / 5000000) = 1/(5000000 / 5004953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15230 : Bounds (990109 / 1000000000) (99011 / 100000000) (Real.log (5004953 / 5000000)) := by
  have h := reflection_log_15230_neg
  have he : Real.log (5004953 / 5000000) = -Real.log (5000000 / 5004953) := by
    rw [show ((5004953 / 5000000) : ℝ) = ((5000000 / 5004953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15231_neg : (99109 / 100000000) ≤ -Real.log (4995047 / 5000000) ∧
    -Real.log (4995047 / 5000000) ≤ (991091 / 1000000000) := by
  have h := checkLog_sound (w := (4953 / 9995047)) (n := 12)
    (lo := (99109 / 100000000)) (hi := (991091 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995047) = 1/(4995047 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15231 : Bounds (-991091 / 1000000000) (-99109 / 100000000) (Real.log (4995047 / 5000000)) := by
  have h := reflection_log_15231_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


