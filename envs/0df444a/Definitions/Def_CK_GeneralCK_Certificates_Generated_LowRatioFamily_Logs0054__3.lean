-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T09:32:44.039545+00:00
-- url     : https://prove2.me/theorems/9f7f2210-688c-4cca-bd62-1df349fa3cdc
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0054 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0055, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0054 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0055, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0056).lean)

import Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0054__3_q01

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0056 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_3584_neg : (193463397 / 1000000000) ≤ -Real.log (8241 / 10000) ∧
    -Real.log (8241 / 10000) ≤ (96731699 / 500000000) := by
  have h := checkLog_sound (w := (1759 / 18241)) (n := 12)
    (lo := (193463397 / 1000000000)) (hi := (96731699 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8241) = 1/(8241 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3584 : Bounds (-96731699 / 500000000) (-193463397 / 1000000000) (Real.log (8241 / 10000)) := by
  have h := reflection_log_3584_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3585_neg : (43971 / 250000000) ≤ -Real.log (10000000 / 10001759) ∧
    -Real.log (10000000 / 10001759) ≤ (35177 / 200000000) := by
  have h := checkLog_sound (w := (1759 / 20001759)) (n := 12)
    (lo := (43971 / 250000000)) (hi := (35177 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001759 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001759 / 10000000) = 1/(10000000 / 10001759) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3585 : Bounds (43971 / 250000000) (35177 / 200000000) (Real.log (10001759 / 10000000)) := by
  have h := reflection_log_3585_neg
  have he : Real.log (10001759 / 10000000) = -Real.log (10000000 / 10001759) := by
    rw [show ((10001759 / 10000000) : ℝ) = ((10000000 / 10001759) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3586_neg : (35183 / 200000000) ≤ -Real.log (9998241 / 10000000) ∧
    -Real.log (9998241 / 10000000) ≤ (43979 / 250000000) := by
  have h := checkLog_sound (w := (1759 / 19998241)) (n := 12)
    (lo := (35183 / 200000000)) (hi := (43979 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998241) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998241) = 1/(9998241 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3586 : Bounds (-43979 / 250000000) (-35183 / 200000000) (Real.log (9998241 / 10000000)) := by
  have h := reflection_log_3586_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3587_neg : (42311179 / 500000000) ≤ -Real.log (500000 / 544153) ∧
    -Real.log (500000 / 544153) ≤ (84622359 / 1000000000) := by
  have h := checkLog_sound (w := (44153 / 1044153)) (n := 12)
    (lo := (42311179 / 500000000)) (hi := (84622359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544153 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544153 / 500000) = 1/(500000 / 544153) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3587 : Bounds (42311179 / 500000000) (84622359 / 1000000000) (Real.log (544153 / 500000)) := by
  have h := reflection_log_3587_neg
  have he : Real.log (544153 / 500000) = -Real.log (500000 / 544153) := by
    rw [show ((544153 / 500000) : ℝ) = ((500000 / 544153) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3588_neg : (92450871 / 1000000000) ≤ -Real.log (455847 / 500000) ∧
    -Real.log (455847 / 500000) ≤ (11556359 / 125000000) := by
  have h := checkLog_sound (w := (44153 / 955847)) (n := 12)
    (lo := (92450871 / 1000000000)) (hi := (11556359 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455847) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455847) = 1/(455847 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3588 : Bounds (-11556359 / 125000000) (-92450871 / 1000000000) (Real.log (455847 / 500000)) := by
  have h := reflection_log_3588_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3589_neg : (42415459 / 500000000) ≤ -Real.log (1000000 / 1088533) ∧
    -Real.log (1000000 / 1088533) ≤ (84830919 / 1000000000) := by
  have h := checkLog_sound (w := (88533 / 2088533)) (n := 12)
    (lo := (42415459 / 500000000)) (hi := (84830919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088533 / 1000000) = 1/(1000000 / 1088533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3589 : Bounds (42415459 / 500000000) (84830919 / 1000000000) (Real.log (1088533 / 1000000)) := by
  have h := reflection_log_3589_neg
  have he : Real.log (1088533 / 1000000) = -Real.log (1000000 / 1088533) := by
    rw [show ((1088533 / 1000000) : ℝ) = ((1000000 / 1088533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3590_neg : (92699889 / 1000000000) ≤ -Real.log (911467 / 1000000) ∧
    -Real.log (911467 / 1000000) ≤ (9269989 / 100000000) := by
  have h := checkLog_sound (w := (88533 / 1911467)) (n := 12)
    (lo := (92699889 / 1000000000)) (hi := (9269989 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911467) = 1/(911467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3590 : Bounds (-9269989 / 100000000) (-92699889 / 1000000000) (Real.log (911467 / 1000000)) := by
  have h := reflection_log_3590_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3591_neg : (7868971 / 1000000000) ≤ -Real.log (992161907911 / 1000000000000) ∧
    -Real.log (992161907911 / 1000000000000) ≤ (1967243 / 250000000) := by
  have h := checkLog_sound (w := (7838092089 / 1992161907911)) (n := 12)
    (lo := (7868971 / 1000000000)) (hi := (1967243 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992161907911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992161907911) = 1/(992161907911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3591 : Bounds (-1967243 / 250000000) (-7868971 / 1000000000) (Real.log (992161907911 / 1000000000000)) := by
  have h := reflection_log_3591_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3592_neg : (244641 / 31250000) ≤ -Real.log (248050512591 / 250000000000) ∧
    -Real.log (248050512591 / 250000000000) ≤ (7828513 / 1000000000) := by
  have h := checkLog_sound (w := (1949487409 / 498050512591)) (n := 12)
    (lo := (244641 / 31250000)) (hi := (7828513 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248050512591) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248050512591) = 1/(248050512591 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3592 : Bounds (-7828513 / 1000000000) (-244641 / 31250000) (Real.log (248050512591 / 250000000000)) := by
  have h := reflection_log_3592_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3593_neg : (17707323 / 100000000) ≤ -Real.log (250000000000 / 298429626607) ∧
    -Real.log (250000000000 / 298429626607) ≤ (177073231 / 1000000000) := by
  have h := checkLog_sound (w := (48429626607 / 548429626607)) (n := 12)
    (lo := (17707323 / 100000000)) (hi := (177073231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298429626607 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298429626607 / 250000000000) = 1/(250000000000 / 298429626607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3593 : Bounds (17707323 / 100000000) (177073231 / 1000000000) (Real.log (298429626607 / 250000000000)) := by
  have h := reflection_log_3593_neg
  have he : Real.log (298429626607 / 250000000000) = -Real.log (250000000000 / 298429626607) := by
    rw [show ((298429626607 / 250000000000) : ℝ) = ((250000000000 / 298429626607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3594_neg : (177530807 / 1000000000) ≤ -Real.log (500000000000 / 597132424981) ∧
    -Real.log (500000000000 / 597132424981) ≤ (22191351 / 125000000) := by
  have h := checkLog_sound (w := (97132424981 / 1097132424981)) (n := 12)
    (lo := (177530807 / 1000000000)) (hi := (22191351 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597132424981 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597132424981 / 500000000000) = 1/(500000000000 / 597132424981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3594 : Bounds (177530807 / 1000000000) (22191351 / 125000000) (Real.log (597132424981 / 500000000000)) := by
  have h := reflection_log_3594_neg
  have he : Real.log (597132424981 / 500000000000) = -Real.log (500000000000 / 597132424981) := by
    rw [show ((597132424981 / 500000000000) : ℝ) = ((500000000000 / 597132424981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3595_neg : (355290827 / 1000000000) ≤ -Real.log (250000000000 / 356648871633) ∧
    -Real.log (250000000000 / 356648871633) ≤ (88822707 / 250000000) := by
  have h := checkLog_sound (w := (106648871633 / 606648871633)) (n := 12)
    (lo := (355290827 / 1000000000)) (hi := (88822707 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356648871633 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(356648871633 / 250000000000) = 1/(250000000000 / 356648871633) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3595 : Bounds (355290827 / 1000000000) (88822707 / 250000000) (Real.log (356648871633 / 250000000000)) := by
  have h := reflection_log_3595_neg
  have he : Real.log (356648871633 / 250000000000) = -Real.log (250000000000 / 356648871633) := by
    rw [show ((356648871633 / 250000000000) : ℝ) = ((250000000000 / 356648871633) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3596_neg : (355497209 / 1000000000) ≤ -Real.log (500000000000 / 713444970271) ∧
    -Real.log (500000000000 / 713444970271) ≤ (35549721 / 100000000) := by
  have h := checkLog_sound (w := (213444970271 / 1213444970271)) (n := 12)
    (lo := (355497209 / 1000000000)) (hi := (35549721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713444970271 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713444970271 / 500000000000) = 1/(500000000000 / 713444970271) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3596 : Bounds (355497209 / 1000000000) (35549721 / 100000000) (Real.log (713444970271 / 500000000000)) := by
  have h := reflection_log_3596_neg
  have he : Real.log (713444970271 / 500000000000) = -Real.log (500000000000 / 713444970271) := by
    rw [show ((713444970271 / 500000000000) : ℝ) = ((500000000000 / 713444970271) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3597_neg : (162118849 / 1000000000) ≤ -Real.log (125 / 147) ∧
    -Real.log (125 / 147) ≤ (3242377 / 20000000) := by
  have h := checkLog_sound (w := (11 / 136)) (n := 12)
    (lo := (162118849 / 1000000000)) (hi := (3242377 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((147 / 125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(147 / 125) = 1/(125 / 147) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3597 : Bounds (162118849 / 1000000000) (3242377 / 20000000) (Real.log (147 / 125)) := by
  have h := reflection_log_3597_neg
  have he : Real.log (147 / 125) = -Real.log (125 / 147) := by
    rw [show ((147 / 125) : ℝ) = ((125 / 147) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3598_neg : (193584749 / 1000000000) ≤ -Real.log (103 / 125) ∧
    -Real.log (103 / 125) ≤ (774339 / 4000000) := by
  have h := checkLog_sound (w := (11 / 114)) (n := 12)
    (lo := (193584749 / 1000000000)) (hi := (774339 / 4000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 103) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125 / 103) = 1/(103 / 125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3598 : Bounds (-774339 / 4000000) (-193584749 / 1000000000) (Real.log (103 / 125)) := by
  have h := reflection_log_3598_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3599_neg : (10999 / 62500000) ≤ -Real.log (62500 / 62511) ∧
    -Real.log (62500 / 62511) ≤ (35197 / 200000000) := by
  have h := checkLog_sound (w := (11 / 125011)) (n := 12)
    (lo := (10999 / 62500000)) (hi := (35197 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62511 / 62500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62511 / 62500) = 1/(62500 / 62511) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3599 : Bounds (10999 / 62500000) (35197 / 200000000) (Real.log (62511 / 62500)) := by
  have h := reflection_log_3599_neg
  have he : Real.log (62511 / 62500) = -Real.log (62500 / 62511) := by
    rw [show ((62511 / 62500) : ℝ) = ((62500 / 62511) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3600_neg : (35203 / 200000000) ≤ -Real.log (62489 / 62500) ∧
    -Real.log (62489 / 62500) ≤ (11001 / 62500000) := by
  have h := checkLog_sound (w := (11 / 124989)) (n := 12)
    (lo := (35203 / 200000000)) (hi := (11001 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 62489) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500 / 62489) = 1/(62489 / 62500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3600 : Bounds (-11001 / 62500000) (-35203 / 200000000) (Real.log (62489 / 62500)) := by
  have h := reflection_log_3600_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3601_neg : (84669219 / 1000000000) ≤ -Real.log (1000000 / 1088357) ∧
    -Real.log (1000000 / 1088357) ≤ (4233461 / 50000000) := by
  have h := checkLog_sound (w := (88357 / 2088357)) (n := 12)
    (lo := (84669219 / 1000000000)) (hi := (4233461 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088357 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088357 / 1000000) = 1/(1000000 / 1088357) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3601 : Bounds (84669219 / 1000000000) (4233461 / 50000000) (Real.log (1088357 / 1000000)) := by
  have h := reflection_log_3601_neg
  have he : Real.log (1088357 / 1000000) = -Real.log (1000000 / 1088357) := by
    rw [show ((1088357 / 1000000) : ℝ) = ((1000000 / 1088357) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3602_neg : (23126703 / 250000000) ≤ -Real.log (911643 / 1000000) ∧
    -Real.log (911643 / 1000000) ≤ (92506813 / 1000000000) := by
  have h := checkLog_sound (w := (88357 / 1911643)) (n := 12)
    (lo := (23126703 / 250000000)) (hi := (92506813 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911643) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911643) = 1/(911643 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3602 : Bounds (-92506813 / 1000000000) (-23126703 / 250000000) (Real.log (911643 / 1000000)) := by
  have h := reflection_log_3602_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3603_neg : (84877769 / 1000000000) ≤ -Real.log (125000 / 136073) ∧
    -Real.log (125000 / 136073) ≤ (8487777 / 100000000) := by
  have h := checkLog_sound (w := (11073 / 261073)) (n := 12)
    (lo := (84877769 / 1000000000)) (hi := (8487777 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136073 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136073 / 125000) = 1/(125000 / 136073) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3603 : Bounds (84877769 / 1000000000) (8487777 / 100000000) (Real.log (136073 / 125000)) := by
  have h := reflection_log_3603_neg
  have he : Real.log (136073 / 125000) = -Real.log (125000 / 136073) := by
    rw [show ((136073 / 125000) : ℝ) = ((125000 / 136073) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3604_neg : (23188961 / 250000000) ≤ -Real.log (113927 / 125000) ∧
    -Real.log (113927 / 125000) ≤ (18551169 / 200000000) := by
  have h := checkLog_sound (w := (11073 / 238927)) (n := 12)
    (lo := (23188961 / 250000000)) (hi := (18551169 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113927) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113927) = 1/(113927 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3604 : Bounds (-18551169 / 200000000) (-23188961 / 250000000) (Real.log (113927 / 125000)) := by
  have h := reflection_log_3604_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3605_neg : (315123 / 40000000) ≤ -Real.log (15502388671 / 15625000000) ∧
    -Real.log (15502388671 / 15625000000) ≤ (1969519 / 250000000) := by
  have h := checkLog_sound (w := (122611329 / 31127388671)) (n := 12)
    (lo := (315123 / 40000000)) (hi := (1969519 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15502388671) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15502388671) = 1/(15502388671 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3605 : Bounds (-1969519 / 250000000) (-315123 / 40000000) (Real.log (15502388671 / 15625000000)) := by
  have h := reflection_log_3605_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3606_neg : (7837593 / 1000000000) ≤ -Real.log (992193040551 / 1000000000000) ∧
    -Real.log (992193040551 / 1000000000000) ≤ (3918797 / 500000000) := by
  have h := checkLog_sound (w := (7806959449 / 1992193040551)) (n := 12)
    (lo := (7837593 / 1000000000)) (hi := (3918797 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992193040551) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992193040551) = 1/(992193040551 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3606 : Bounds (-3918797 / 500000000) (-7837593 / 1000000000) (Real.log (992193040551 / 1000000000000)) := by
  have h := reflection_log_3606_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3607_neg : (5536751 / 31250000) ≤ -Real.log (250000000000 / 298460307379) ∧
    -Real.log (250000000000 / 298460307379) ≤ (177176033 / 1000000000) := by
  have h := checkLog_sound (w := (48460307379 / 548460307379)) (n := 12)
    (lo := (5536751 / 31250000)) (hi := (177176033 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298460307379 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298460307379 / 250000000000) = 1/(250000000000 / 298460307379) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3607 : Bounds (5536751 / 31250000) (177176033 / 1000000000) (Real.log (298460307379 / 250000000000)) := by
  have h := reflection_log_3607_neg
  have he : Real.log (298460307379 / 250000000000) = -Real.log (250000000000 / 298460307379) := by
    rw [show ((298460307379 / 250000000000) : ℝ) = ((250000000000 / 298460307379) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3608_neg : (88816807 / 500000000) ≤ -Real.log (250000000000 / 298596908547) ∧
    -Real.log (250000000000 / 298596908547) ≤ (35526723 / 200000000) := by
  have h := checkLog_sound (w := (48596908547 / 548596908547)) (n := 12)
    (lo := (88816807 / 500000000)) (hi := (35526723 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((298596908547 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(298596908547 / 250000000000) = 1/(250000000000 / 298596908547) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3608 : Bounds (88816807 / 500000000) (35526723 / 200000000) (Real.log (298596908547 / 250000000000)) := by
  have h := reflection_log_3608_neg
  have he : Real.log (298596908547 / 250000000000) = -Real.log (250000000000 / 298596908547) := by
    rw [show ((298596908547 / 250000000000) : ℝ) = ((250000000000 / 298596908547) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3609_neg : (355497209 / 1000000000) ≤ -Real.log (50000000000 / 71344497027) ∧
    -Real.log (50000000000 / 71344497027) ≤ (35549721 / 100000000) := by
  have h := checkLog_sound (w := (21344497027 / 121344497027)) (n := 12)
    (lo := (355497209 / 1000000000)) (hi := (35549721 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71344497027 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71344497027 / 50000000000) = 1/(50000000000 / 71344497027) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3609 : Bounds (355497209 / 1000000000) (35549721 / 100000000) (Real.log (71344497027 / 50000000000)) := by
  have h := reflection_log_3609_neg
  have he : Real.log (71344497027 / 50000000000) = -Real.log (50000000000 / 71344497027) := by
    rw [show ((71344497027 / 50000000000) : ℝ) = ((50000000000 / 71344497027) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3610_neg : (177851799 / 500000000) ≤ -Real.log (50000000000 / 71359223301) ∧
    -Real.log (50000000000 / 71359223301) ≤ (355703599 / 1000000000) := by
  have h := checkLog_sound (w := (21359223301 / 121359223301)) (n := 12)
    (lo := (177851799 / 500000000)) (hi := (355703599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((71359223301 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(71359223301 / 50000000000) = 1/(50000000000 / 71359223301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3610 : Bounds (177851799 / 500000000) (355703599 / 1000000000) (Real.log (71359223301 / 50000000000)) := by
  have h := reflection_log_3610_neg
  have he : Real.log (71359223301 / 50000000000) = -Real.log (50000000000 / 71359223301) := by
    rw [show ((71359223301 / 50000000000) : ℝ) = ((50000000000 / 71359223301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3611_neg : (162203879 / 1000000000) ≤ -Real.log (10000 / 11761) ∧
    -Real.log (10000 / 11761) ≤ (4055097 / 25000000) := by
  have h := checkLog_sound (w := (1761 / 21761)) (n := 12)
    (lo := (162203879 / 1000000000)) (hi := (4055097 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11761 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11761 / 10000) = 1/(10000 / 11761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3611 : Bounds (162203879 / 1000000000) (4055097 / 25000000) (Real.log (11761 / 10000)) := by
  have h := reflection_log_3611_neg
  have he : Real.log (11761 / 10000) = -Real.log (10000 / 11761) := by
    rw [show ((11761 / 10000) : ℝ) = ((10000 / 11761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3612_neg : (38741223 / 200000000) ≤ -Real.log (8239 / 10000) ∧
    -Real.log (8239 / 10000) ≤ (48426529 / 250000000) := by
  have h := checkLog_sound (w := (1761 / 18239)) (n := 12)
    (lo := (38741223 / 200000000)) (hi := (48426529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8239) = 1/(8239 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3612 : Bounds (-48426529 / 250000000) (-38741223 / 200000000) (Real.log (8239 / 10000)) := by
  have h := reflection_log_3612_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3613_neg : (44021 / 250000000) ≤ -Real.log (10000000 / 10001761) ∧
    -Real.log (10000000 / 10001761) ≤ (35217 / 200000000) := by
  have h := checkLog_sound (w := (1761 / 20001761)) (n := 12)
    (lo := (44021 / 250000000)) (hi := (35217 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001761 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001761 / 10000000) = 1/(10000000 / 10001761) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3613 : Bounds (44021 / 250000000) (35217 / 200000000) (Real.log (10001761 / 10000000)) := by
  have h := reflection_log_3613_neg
  have he : Real.log (10001761 / 10000000) = -Real.log (10000000 / 10001761) := by
    rw [show ((10001761 / 10000000) : ℝ) = ((10000000 / 10001761) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3614_neg : (35223 / 200000000) ≤ -Real.log (9998239 / 10000000) ∧
    -Real.log (9998239 / 10000000) ≤ (44029 / 250000000) := by
  have h := checkLog_sound (w := (1761 / 19998239)) (n := 12)
    (lo := (35223 / 200000000)) (hi := (44029 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998239) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998239) = 1/(9998239 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3614 : Bounds (-44029 / 250000000) (-35223 / 200000000) (Real.log (9998239 / 10000000)) := by
  have h := reflection_log_3614_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3615_neg : (42358039 / 500000000) ≤ -Real.log (125000 / 136051) ∧
    -Real.log (125000 / 136051) ≤ (84716079 / 1000000000) := by
  have h := checkLog_sound (w := (11051 / 261051)) (n := 12)
    (lo := (42358039 / 500000000)) (hi := (84716079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((136051 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(136051 / 125000) = 1/(125000 / 136051) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3615 : Bounds (42358039 / 500000000) (84716079 / 1000000000) (Real.log (136051 / 125000)) := by
  have h := reflection_log_3615_neg
  have he : Real.log (136051 / 125000) = -Real.log (125000 / 136051) := by
    rw [show ((136051 / 125000) : ℝ) = ((125000 / 136051) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3616_neg : (92562757 / 1000000000) ≤ -Real.log (113949 / 125000) ∧
    -Real.log (113949 / 125000) ≤ (46281379 / 500000000) := by
  have h := checkLog_sound (w := (11051 / 238949)) (n := 12)
    (lo := (92562757 / 1000000000)) (hi := (46281379 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 113949) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(125000 / 113949) = 1/(113949 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3616 : Bounds (-46281379 / 500000000) (-92562757 / 1000000000) (Real.log (113949 / 125000)) := by
  have h := reflection_log_3616_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3617_neg : (84924617 / 1000000000) ≤ -Real.log (200000 / 217727) ∧
    -Real.log (200000 / 217727) ≤ (42462309 / 500000000) := by
  have h := checkLog_sound (w := (17727 / 417727)) (n := 12)
    (lo := (84924617 / 1000000000)) (hi := (42462309 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((217727 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(217727 / 200000) = 1/(200000 / 217727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3617 : Bounds (84924617 / 1000000000) (42462309 / 500000000) (Real.log (217727 / 200000)) := by
  have h := reflection_log_3617_neg
  have he : Real.log (217727 / 200000) = -Real.log (200000 / 217727) := by
    rw [show ((217727 / 200000) : ℝ) = ((200000 / 217727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3618_neg : (92811803 / 1000000000) ≤ -Real.log (182273 / 200000) ∧
    -Real.log (182273 / 200000) ≤ (23202951 / 250000000) := by
  have h := checkLog_sound (w := (17727 / 382273)) (n := 12)
    (lo := (92811803 / 1000000000)) (hi := (23202951 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 182273) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 182273) = 1/(182273 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3618 : Bounds (-23202951 / 250000000) (-92811803 / 1000000000) (Real.log (182273 / 200000)) := by
  have h := reflection_log_3618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3619_neg : (1577437 / 200000000) ≤ -Real.log (39685753471 / 40000000000) ∧
    -Real.log (39685753471 / 40000000000) ≤ (3943593 / 500000000) := by
  have h := checkLog_sound (w := (314246529 / 79685753471)) (n := 12)
    (lo := (1577437 / 200000000)) (hi := (3943593 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39685753471) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39685753471) = 1/(39685753471 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3619 : Bounds (-3943593 / 500000000) (-1577437 / 200000000) (Real.log (39685753471 / 40000000000)) := by
  have h := reflection_log_3619_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3620_neg : (7846679 / 1000000000) ≤ -Real.log (15502875399 / 15625000000) ∧
    -Real.log (15502875399 / 15625000000) ≤ (196167 / 25000000) := by
  have h := checkLog_sound (w := (122124601 / 31127875399)) (n := 12)
    (lo := (7846679 / 1000000000)) (hi := (196167 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 15502875399) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 15502875399) = 1/(15502875399 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3620 : Bounds (-196167 / 25000000) (-7846679 / 1000000000) (Real.log (15502875399 / 15625000000)) := by
  have h := reflection_log_3620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3621_neg : (35455767 / 200000000) ≤ -Real.log (500000000000 / 596981983167) ∧
    -Real.log (500000000000 / 596981983167) ≤ (44319709 / 250000000) := by
  have h := checkLog_sound (w := (96981983167 / 1096981983167)) (n := 12)
    (lo := (35455767 / 200000000)) (hi := (44319709 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((596981983167 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(596981983167 / 500000000000) = 1/(500000000000 / 596981983167) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3621 : Bounds (35455767 / 200000000) (44319709 / 250000000) (Real.log (596981983167 / 500000000000)) := by
  have h := reflection_log_3621_neg
  have he : Real.log (596981983167 / 500000000000) = -Real.log (500000000000 / 596981983167) := by
    rw [show ((596981983167 / 500000000000) : ℝ) = ((500000000000 / 596981983167) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3622_neg : (177736421 / 1000000000) ≤ -Real.log (500000000000 / 597255216077) ∧
    -Real.log (500000000000 / 597255216077) ≤ (88868211 / 500000000) := by
  have h := checkLog_sound (w := (97255216077 / 1097255216077)) (n := 12)
    (lo := (177736421 / 1000000000)) (hi := (88868211 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597255216077 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597255216077 / 500000000000) = 1/(500000000000 / 597255216077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3622 : Bounds (177736421 / 1000000000) (88868211 / 500000000) (Real.log (597255216077 / 500000000000)) := by
  have h := reflection_log_3622_neg
  have he : Real.log (597255216077 / 500000000000) = -Real.log (500000000000 / 597255216077) := by
    rw [show ((597255216077 / 500000000000) : ℝ) = ((500000000000 / 597255216077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3623_neg : (177851799 / 500000000) ≤ -Real.log (500000000000 / 713592233009) ∧
    -Real.log (500000000000 / 713592233009) ≤ (355703599 / 1000000000) := by
  have h := checkLog_sound (w := (213592233009 / 1213592233009)) (n := 12)
    (lo := (177851799 / 500000000)) (hi := (355703599 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713592233009 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713592233009 / 500000000000) = 1/(500000000000 / 713592233009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3623 : Bounds (177851799 / 500000000) (355703599 / 1000000000) (Real.log (713592233009 / 500000000000)) := by
  have h := reflection_log_3623_neg
  have he : Real.log (713592233009 / 500000000000) = -Real.log (500000000000 / 713592233009) := by
    rw [show ((713592233009 / 500000000000) : ℝ) = ((500000000000 / 713592233009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3624_neg : (71181999 / 200000000) ≤ -Real.log (500000000000 / 713739531497) ∧
    -Real.log (500000000000 / 713739531497) ≤ (88977499 / 250000000) := by
  have h := checkLog_sound (w := (213739531497 / 1213739531497)) (n := 12)
    (lo := (71181999 / 200000000)) (hi := (88977499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((713739531497 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(713739531497 / 500000000000) = 1/(500000000000 / 713739531497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3624 : Bounds (71181999 / 200000000) (88977499 / 250000000) (Real.log (713739531497 / 500000000000)) := by
  have h := reflection_log_3624_neg
  have he : Real.log (713739531497 / 500000000000) = -Real.log (500000000000 / 713739531497) := by
    rw [show ((713739531497 / 500000000000) : ℝ) = ((500000000000 / 713739531497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3625_neg : (162288903 / 1000000000) ≤ -Real.log (5000 / 5881) ∧
    -Real.log (5000 / 5881) ≤ (20286113 / 125000000) := by
  have h := checkLog_sound (w := (881 / 10881)) (n := 12)
    (lo := (162288903 / 1000000000)) (hi := (20286113 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5881 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5881 / 5000) = 1/(5000 / 5881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3625 : Bounds (162288903 / 1000000000) (20286113 / 125000000) (Real.log (5881 / 5000)) := by
  have h := reflection_log_3625_neg
  have he : Real.log (5881 / 5000) = -Real.log (5000 / 5881) := by
    rw [show ((5881 / 5000) : ℝ) = ((5000 / 5881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3626_neg : (24228437 / 125000000) ≤ -Real.log (4119 / 5000) ∧
    -Real.log (4119 / 5000) ≤ (193827497 / 1000000000) := by
  have h := checkLog_sound (w := (881 / 9119)) (n := 12)
    (lo := (24228437 / 125000000)) (hi := (193827497 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000 / 4119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000 / 4119) = 1/(4119 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3626 : Bounds (-193827497 / 1000000000) (-24228437 / 125000000) (Real.log (4119 / 5000)) := by
  have h := reflection_log_3626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3627_neg : (22023 / 125000000) ≤ -Real.log (5000000 / 5000881) ∧
    -Real.log (5000000 / 5000881) ≤ (35237 / 200000000) := by
  have h := checkLog_sound (w := (881 / 10000881)) (n := 12)
    (lo := (22023 / 125000000)) (hi := (35237 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000881 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000881 / 5000000) = 1/(5000000 / 5000881) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3627 : Bounds (22023 / 125000000) (35237 / 200000000) (Real.log (5000881 / 5000000)) := by
  have h := reflection_log_3627_neg
  have he : Real.log (5000881 / 5000000) = -Real.log (5000000 / 5000881) := by
    rw [show ((5000881 / 5000000) : ℝ) = ((5000000 / 5000881) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3628_neg : (35243 / 200000000) ≤ -Real.log (4999119 / 5000000) ∧
    -Real.log (4999119 / 5000000) ≤ (22027 / 125000000) := by
  have h := checkLog_sound (w := (881 / 9999119)) (n := 12)
    (lo := (35243 / 200000000)) (hi := (22027 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4999119) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4999119) = 1/(4999119 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3628 : Bounds (-22027 / 125000000) (-35243 / 200000000) (Real.log (4999119 / 5000000)) := by
  have h := reflection_log_3628_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3629_neg : (42381467 / 500000000) ≤ -Real.log (1000000 / 1088459) ∧
    -Real.log (1000000 / 1088459) ≤ (16952587 / 200000000) := by
  have h := checkLog_sound (w := (88459 / 2088459)) (n := 12)
    (lo := (42381467 / 500000000)) (hi := (16952587 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088459 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088459 / 1000000) = 1/(1000000 / 1088459) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3629 : Bounds (42381467 / 500000000) (16952587 / 200000000) (Real.log (1088459 / 1000000)) := by
  have h := reflection_log_3629_neg
  have he : Real.log (1088459 / 1000000) = -Real.log (1000000 / 1088459) := by
    rw [show ((1088459 / 1000000) : ℝ) = ((1000000 / 1088459) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3630_neg : (18523741 / 200000000) ≤ -Real.log (911541 / 1000000) ∧
    -Real.log (911541 / 1000000) ≤ (46309353 / 500000000) := by
  have h := checkLog_sound (w := (88459 / 1911541)) (n := 12)
    (lo := (18523741 / 200000000)) (hi := (46309353 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911541) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911541) = 1/(911541 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3630 : Bounds (-46309353 / 500000000) (-18523741 / 200000000) (Real.log (911541 / 1000000)) := by
  have h := reflection_log_3630_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3631_neg : (10621433 / 125000000) ≤ -Real.log (500000 / 544343) ∧
    -Real.log (500000 / 544343) ≤ (16994293 / 200000000) := by
  have h := checkLog_sound (w := (44343 / 1044343)) (n := 12)
    (lo := (10621433 / 125000000)) (hi := (16994293 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((544343 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(544343 / 500000) = 1/(500000 / 544343) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3631 : Bounds (10621433 / 125000000) (16994293 / 200000000) (Real.log (544343 / 500000)) := by
  have h := reflection_log_3631_neg
  have he : Real.log (544343 / 500000) = -Real.log (500000 / 544343) := by
    rw [show ((544343 / 500000) : ℝ) = ((500000 / 544343) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3632_neg : (23216941 / 250000000) ≤ -Real.log (455657 / 500000) ∧
    -Real.log (455657 / 500000) ≤ (18573553 / 200000000) := by
  have h := checkLog_sound (w := (44343 / 955657)) (n := 12)
    (lo := (23216941 / 250000000)) (hi := (18573553 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 455657) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 455657) = 1/(455657 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3632 : Bounds (-18573553 / 200000000) (-23216941 / 250000000) (Real.log (455657 / 500000)) := by
  have h := reflection_log_3632_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3633_neg : (78963 / 10000000) ≤ -Real.log (248033698351 / 250000000000) ∧
    -Real.log (248033698351 / 250000000000) ≤ (7896301 / 1000000000) := by
  have h := checkLog_sound (w := (1966301649 / 498033698351)) (n := 12)
    (lo := (78963 / 10000000)) (hi := (7896301 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 248033698351) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 248033698351) = 1/(248033698351 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3633 : Bounds (-7896301 / 1000000000) (-78963 / 10000000) (Real.log (248033698351 / 250000000000)) := by
  have h := reflection_log_3633_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3634_neg : (785577 / 100000000) ≤ -Real.log (992175005319 / 1000000000000) ∧
    -Real.log (992175005319 / 1000000000000) ≤ (7855771 / 1000000000) := by
  have h := checkLog_sound (w := (7824994681 / 1992175005319)) (n := 12)
    (lo := (785577 / 100000000)) (hi := (7855771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992175005319) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992175005319) = 1/(992175005319 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3634 : Bounds (-7855771 / 1000000000) (-785577 / 100000000) (Real.log (992175005319 / 1000000000000)) := by
  have h := reflection_log_3634_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3635_neg : (177381639 / 1000000000) ≤ -Real.log (125000000000 / 149260839611) ∧
    -Real.log (125000000000 / 149260839611) ≤ (4434541 / 25000000) := by
  have h := checkLog_sound (w := (24260839611 / 274260839611)) (n := 12)
    (lo := (177381639 / 1000000000)) (hi := (4434541 / 25000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149260839611 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(149260839611 / 125000000000) = 1/(125000000000 / 149260839611) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3635 : Bounds (177381639 / 1000000000) (4434541 / 25000000) (Real.log (149260839611 / 125000000000)) := by
  have h := reflection_log_3635_neg
  have he : Real.log (149260839611 / 125000000000) = -Real.log (125000000000 / 149260839611) := by
    rw [show ((149260839611 / 125000000000) : ℝ) = ((125000000000 / 149260839611) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3636_neg : (177839229 / 1000000000) ≤ -Real.log (500000000000 / 597316621933) ∧
    -Real.log (500000000000 / 597316621933) ≤ (17783923 / 100000000) := by
  have h := checkLog_sound (w := (97316621933 / 1097316621933)) (n := 12)
    (lo := (177839229 / 1000000000)) (hi := (17783923 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((597316621933 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(597316621933 / 500000000000) = 1/(500000000000 / 597316621933) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3636 : Bounds (177839229 / 1000000000) (17783923 / 100000000) (Real.log (597316621933 / 500000000000)) := by
  have h := reflection_log_3636_neg
  have he : Real.log (597316621933 / 500000000000) = -Real.log (500000000000 / 597316621933) := by
    rw [show ((597316621933 / 500000000000) : ℝ) = ((500000000000 / 597316621933) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3637_neg : (71181999 / 200000000) ≤ -Real.log (62500000000 / 89217441437) ∧
    -Real.log (62500000000 / 89217441437) ≤ (88977499 / 250000000) := by
  have h := checkLog_sound (w := (26717441437 / 151717441437)) (n := 12)
    (lo := (71181999 / 200000000)) (hi := (88977499 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((89217441437 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(89217441437 / 62500000000) = 1/(62500000000 / 89217441437) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3637 : Bounds (71181999 / 200000000) (88977499 / 250000000) (Real.log (89217441437 / 62500000000)) := by
  have h := reflection_log_3637_neg
  have he : Real.log (89217441437 / 62500000000) = -Real.log (62500000000 / 89217441437) := by
    rw [show ((89217441437 / 62500000000) : ℝ) = ((62500000000 / 89217441437) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3638_neg : (890291 / 2500000) ≤ -Real.log (100000000000 / 142777373149) ∧
    -Real.log (100000000000 / 142777373149) ≤ (356116401 / 1000000000) := by
  have h := checkLog_sound (w := (42777373149 / 242777373149)) (n := 12)
    (lo := (890291 / 2500000)) (hi := (356116401 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142777373149 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(142777373149 / 100000000000) = 1/(100000000000 / 142777373149) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3638 : Bounds (890291 / 2500000) (356116401 / 1000000000) (Real.log (142777373149 / 100000000000)) := by
  have h := reflection_log_3638_neg
  have he : Real.log (142777373149 / 100000000000) = -Real.log (100000000000 / 142777373149) := by
    rw [show ((142777373149 / 100000000000) : ℝ) = ((100000000000 / 142777373149) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3639_neg : (81186959 / 500000000) ≤ -Real.log (10000 / 11763) ∧
    -Real.log (10000 / 11763) ≤ (162373919 / 1000000000) := by
  have h := checkLog_sound (w := (1763 / 21763)) (n := 12)
    (lo := (81186959 / 500000000)) (hi := (162373919 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((11763 / 10000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(11763 / 10000) = 1/(10000 / 11763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3639 : Bounds (81186959 / 500000000) (162373919 / 1000000000) (Real.log (11763 / 10000)) := by
  have h := reflection_log_3639_neg
  have he : Real.log (11763 / 10000) = -Real.log (10000 / 11763) := by
    rw [show ((11763 / 10000) : ℝ) = ((10000 / 11763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3640_neg : (193948893 / 1000000000) ≤ -Real.log (8237 / 10000) ∧
    -Real.log (8237 / 10000) ≤ (96974447 / 500000000) := by
  have h := checkLog_sound (w := (1763 / 18237)) (n := 12)
    (lo := (193948893 / 1000000000)) (hi := (96974447 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000 / 8237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000 / 8237) = 1/(8237 / 10000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3640 : Bounds (-96974447 / 500000000) (-193948893 / 1000000000) (Real.log (8237 / 10000)) := by
  have h := reflection_log_3640_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3641_neg : (44071 / 250000000) ≤ -Real.log (10000000 / 10001763) ∧
    -Real.log (10000000 / 10001763) ≤ (35257 / 200000000) := by
  have h := checkLog_sound (w := (1763 / 20001763)) (n := 12)
    (lo := (44071 / 250000000)) (hi := (35257 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10001763 / 10000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10001763 / 10000000) = 1/(10000000 / 10001763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3641 : Bounds (44071 / 250000000) (35257 / 200000000) (Real.log (10001763 / 10000000)) := by
  have h := reflection_log_3641_neg
  have he : Real.log (10001763 / 10000000) = -Real.log (10000000 / 10001763) := by
    rw [show ((10001763 / 10000000) : ℝ) = ((10000000 / 10001763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3642_neg : (35263 / 200000000) ≤ -Real.log (9998237 / 10000000) ∧
    -Real.log (9998237 / 10000000) ≤ (44079 / 250000000) := by
  have h := checkLog_sound (w := (1763 / 19998237)) (n := 12)
    (lo := (35263 / 200000000)) (hi := (44079 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10000000 / 9998237) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10000000 / 9998237) = 1/(9998237 / 10000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3642 : Bounds (-44079 / 250000000) (-35263 / 200000000) (Real.log (9998237 / 10000000)) := by
  have h := reflection_log_3642_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3643_neg : (21202447 / 250000000) ≤ -Real.log (100000 / 108851) ∧
    -Real.log (100000 / 108851) ≤ (84809789 / 1000000000) := by
  have h := checkLog_sound (w := (8851 / 208851)) (n := 12)
    (lo := (21202447 / 250000000)) (hi := (84809789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((108851 / 100000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(108851 / 100000) = 1/(100000 / 108851) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3643 : Bounds (21202447 / 250000000) (84809789 / 1000000000) (Real.log (108851 / 100000)) := by
  have h := reflection_log_3643_neg
  have he : Real.log (108851 / 100000) = -Real.log (100000 / 108851) := by
    rw [show ((108851 / 100000) : ℝ) = ((100000 / 108851) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3644_neg : (18534931 / 200000000) ≤ -Real.log (91149 / 100000) ∧
    -Real.log (91149 / 100000) ≤ (2896083 / 31250000) := by
  have h := checkLog_sound (w := (8851 / 191149)) (n := 12)
    (lo := (18534931 / 200000000)) (hi := (2896083 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 91149) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(100000 / 91149) = 1/(91149 / 100000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3644 : Bounds (-2896083 / 31250000) (-18534931 / 200000000) (Real.log (91149 / 100000)) := by
  have h := reflection_log_3644_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3645_neg : (21254577 / 250000000) ≤ -Real.log (1000000 / 1088737) ∧
    -Real.log (1000000 / 1088737) ≤ (85018309 / 1000000000) := by
  have h := checkLog_sound (w := (88737 / 2088737)) (n := 12)
    (lo := (21254577 / 250000000)) (hi := (85018309 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1088737 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1088737 / 1000000) = 1/(1000000 / 1088737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3645 : Bounds (21254577 / 250000000) (85018309 / 1000000000) (Real.log (1088737 / 1000000)) := by
  have h := reflection_log_3645_neg
  have he : Real.log (1088737 / 1000000) = -Real.log (1000000 / 1088737) := by
    rw [show ((1088737 / 1000000) : ℝ) = ((1000000 / 1088737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_3646_neg : (92923729 / 1000000000) ≤ -Real.log (911263 / 1000000) ∧
    -Real.log (911263 / 1000000) ≤ (9292373 / 100000000) := by
  have h := checkLog_sound (w := (88737 / 1911263)) (n := 12)
    (lo := (92923729 / 1000000000)) (hi := (9292373 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 911263) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 911263) = 1/(911263 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3646 : Bounds (-9292373 / 100000000) (-92923729 / 1000000000) (Real.log (911263 / 1000000)) := by
  have h := reflection_log_3646_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_3647_neg : (395271 / 50000000) ≤ -Real.log (992125744831 / 1000000000000) ∧
    -Real.log (992125744831 / 1000000000000) ≤ (7905421 / 1000000000) := by
  have h := checkLog_sound (w := (7874255169 / 1992125744831)) (n := 12)
    (lo := (395271 / 50000000)) (hi := (7905421 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 992125744831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 992125744831) = 1/(992125744831 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_3647 : Bounds (-7905421 / 1000000000) (-395271 / 50000000) (Real.log (992125744831 / 1000000000000)) := by
  have h := reflection_log_3647_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end


