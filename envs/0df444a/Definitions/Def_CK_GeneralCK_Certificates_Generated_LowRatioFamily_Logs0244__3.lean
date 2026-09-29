-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0244__3
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0244__3
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T05:57:43.887372+00:00
-- url     : https://prove2.me/theorems/09193909-3631-4366-95c1-1911859e83e4
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0244 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0245, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0244 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0245, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0246)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0244 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0245, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0246)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0244 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0245, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0246) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0244 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0245, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0246).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0244 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15616_neg : (6212606091 / 1000000000) ≤ -Real.log (1 / 499) ∧
    -Real.log (1 / 499) ≤ (62126061 / 10000000) := by
  have h := checkLog_sound (w := (243 / 755)) (n := 12)
    (lo := (667428651 / 1000000000)) (hi := (166857163 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((499 / 256) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(499 / 256) = 1/(1 / 499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15616 : Bounds (6212606091 / 1000000000) (62126061 / 10000000) (Real.log (499 / 1)) := by
  have h := reflection_log_15616_neg
  have he : Real.log (499 / 1) = -Real.log (1 / 499) := by
    rw [show ((499 / 1) : ℝ) = ((1 / 499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15617_neg : (691245373 / 1000000000) ≤ -Real.log (5000 / 9981) ∧
    -Real.log (5000 / 9981) ≤ (345622687 / 500000000) := by
  have h := checkLog_sound (w := (4981 / 14981)) (n := 12)
    (lo := (691245373 / 1000000000)) (hi := (345622687 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9981 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9981 / 5000) = 1/(5000 / 9981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15617 : Bounds (691245373 / 1000000000) (345622687 / 500000000) (Real.log (9981 / 5000)) := by
  have h := reflection_log_15617_neg
  have he : Real.log (9981 / 5000) = -Real.log (5000 / 9981) := by
    rw [show ((9981 / 5000) : ℝ) = ((5000 / 9981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15618_neg : (5572754207 / 1000000000) ≤ -Real.log (19 / 5000) ∧
    -Real.log (19 / 5000) ≤ (696594277 / 125000000) := by
  have h := checkLog_sound (w := (17 / 1233)) (n := 12)
    (lo := (27576767 / 1000000000)) (hi := (430887 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 608) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 608) = 1/(19 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15618 : Bounds (-696594277 / 125000000) (-5572754207 / 1000000000) (Real.log (19 / 5000)) := by
  have h := reflection_log_15618_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15619_neg : (124463 / 125000000) ≤ -Real.log (5000000 / 5004981) ∧
    -Real.log (5000000 / 5004981) ≤ (199141 / 200000000) := by
  have h := checkLog_sound (w := (4981 / 10004981)) (n := 12)
    (lo := (124463 / 125000000)) (hi := (199141 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004981 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004981 / 5000000) = 1/(5000000 / 5004981) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15619 : Bounds (124463 / 125000000) (199141 / 200000000) (Real.log (5004981 / 5000000)) := by
  have h := reflection_log_15619_neg
  have he : Real.log (5004981 / 5000000) = -Real.log (5000000 / 5004981) := by
    rw [show ((5004981 / 5000000) : ℝ) = ((5000000 / 5004981) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15620_neg : (124587 / 125000000) ≤ -Real.log (4995019 / 5000000) ∧
    -Real.log (4995019 / 5000000) ≤ (996697 / 1000000000) := by
  have h := checkLog_sound (w := (4981 / 9995019)) (n := 12)
    (lo := (124587 / 125000000)) (hi := (996697 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995019) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995019) = 1/(4995019 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15620 : Bounds (-996697 / 1000000000) (-124587 / 125000000) (Real.log (4995019 / 5000000)) := by
  have h := reflection_log_15620_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15621_neg : (501383587 / 1000000000) ≤ -Real.log (250000 / 412751) ∧
    -Real.log (250000 / 412751) ≤ (125345897 / 250000000) := by
  have h := checkLog_sound (w := (162751 / 662751)) (n := 12)
    (lo := (501383587 / 1000000000)) (hi := (125345897 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((412751 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(412751 / 250000) = 1/(250000 / 412751) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15621 : Bounds (501383587 / 1000000000) (125345897 / 250000000) (Real.log (412751 / 250000)) := by
  have h := reflection_log_15621_neg
  have he : Real.log (412751 / 250000) = -Real.log (250000 / 412751) := by
    rw [show ((412751 / 250000) : ℝ) = ((250000 / 412751) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15622_neg : (1052694817 / 1000000000) ≤ -Real.log (87249 / 250000) ∧
    -Real.log (87249 / 250000) ≤ (1052694819 / 1000000000) := by
  have h := checkLog_sound (w := (37751 / 212249)) (n := 12)
    (lo := (359547637 / 1000000000)) (hi := (179773819 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 87249) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 87249) = 1/(87249 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15622 : Bounds (-1052694819 / 1000000000) (-1052694817 / 1000000000) (Real.log (87249 / 250000)) := by
  have h := reflection_log_15622_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15623_neg : (501964277 / 1000000000) ≤ -Real.log (1000000 / 1651963) ∧
    -Real.log (1000000 / 1651963) ≤ (250982139 / 500000000) := by
  have h := checkLog_sound (w := (651963 / 2651963)) (n := 12)
    (lo := (501964277 / 1000000000)) (hi := (250982139 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651963 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651963 / 1000000) = 1/(1000000 / 1651963) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15623 : Bounds (501964277 / 1000000000) (250982139 / 500000000) (Real.log (1651963 / 1000000)) := by
  have h := reflection_log_15623_neg
  have he : Real.log (1651963 / 1000000) = -Real.log (1000000 / 1651963) := by
    rw [show ((1651963 / 1000000) : ℝ) = ((1000000 / 1651963) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15624_neg : (527723241 / 500000000) ≤ -Real.log (348037 / 1000000) ∧
    -Real.log (348037 / 1000000) ≤ (263861621 / 250000000) := by
  have h := checkLog_sound (w := (151963 / 848037)) (n := 12)
    (lo := (181149651 / 500000000)) (hi := (362299303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348037) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348037) = 1/(348037 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15624 : Bounds (-263861621 / 250000000) (-527723241 / 500000000) (Real.log (348037 / 1000000)) := by
  have h := reflection_log_15624_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15625_neg : (110696441 / 200000000) ≤ -Real.log (574944246631 / 1000000000000) ∧
    -Real.log (574944246631 / 1000000000000) ≤ (276741103 / 500000000) := by
  have h := checkLog_sound (w := (425055753369 / 1574944246631)) (n := 12)
    (lo := (110696441 / 200000000)) (hi := (276741103 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 574944246631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 574944246631) = 1/(574944246631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15625 : Bounds (-276741103 / 500000000) (-110696441 / 200000000) (Real.log (574944246631 / 1000000000000)) := by
  have h := reflection_log_15625_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15626_neg : (55131123 / 100000000) ≤ -Real.log (36012111999 / 62500000000) ∧
    -Real.log (36012111999 / 62500000000) ≤ (551311231 / 1000000000) := by
  have h := checkLog_sound (w := (26487888001 / 98512111999)) (n := 12)
    (lo := (55131123 / 100000000)) (hi := (551311231 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 36012111999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 36012111999) = 1/(36012111999 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15626 : Bounds (-551311231 / 1000000000) (-55131123 / 100000000) (Real.log (36012111999 / 62500000000)) := by
  have h := reflection_log_15626_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15627_neg : (388519601 / 250000000) ≤ -Real.log (500000000000 / 2365362353723) ∧
    -Real.log (500000000000 / 2365362353723) ≤ (1554078407 / 1000000000) := by
  have h := checkLog_sound (w := (365362353723 / 4365362353723)) (n := 12)
    (lo := (41946011 / 250000000)) (hi := (33556809 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2365362353723 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2365362353723 / 2000000000000) = 1/(500000000000 / 2365362353723) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15627 : Bounds (388519601 / 250000000) (1554078407 / 1000000000) (Real.log (2365362353723 / 500000000000)) := by
  have h := reflection_log_15627_neg
  have he : Real.log (2365362353723 / 500000000000) = -Real.log (500000000000 / 2365362353723) := by
    rw [show ((2365362353723 / 500000000000) : ℝ) = ((500000000000 / 2365362353723) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15628_neg : (1557410759 / 1000000000) ≤ -Real.log (100000000000 / 474651545669) ∧
    -Real.log (100000000000 / 474651545669) ≤ (778705381 / 500000000) := by
  have h := checkLog_sound (w := (74651545669 / 874651545669)) (n := 12)
    (lo := (171116399 / 1000000000)) (hi := (427791 / 2500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((474651545669 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(474651545669 / 400000000000) = 1/(100000000000 / 474651545669) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15628 : Bounds (1557410759 / 1000000000) (778705381 / 500000000) (Real.log (474651545669 / 100000000000)) := by
  have h := reflection_log_15628_neg
  have he : Real.log (474651545669 / 100000000000) = -Real.log (100000000000 / 474651545669) := by
    rw [show ((474651545669 / 100000000000) : ℝ) = ((100000000000 / 474651545669) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15629_neg : (313199979 / 50000000) ≤ -Real.log (500000000000 / 262657894736843) ∧
    -Real.log (500000000000 / 262657894736843) ≤ (626399959 / 100000000) := by
  have h := checkLog_sound (w := (6657894736843 / 518657894736843)) (n := 12)
    (lo := (320937 / 12500000)) (hi := (25674961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((262657894736843 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(262657894736843 / 256000000000000) = 1/(500000000000 / 262657894736843) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15629 : Bounds (313199979 / 50000000) (626399959 / 100000000) (Real.log (262657894736843 / 500000000000)) := by
  have h := reflection_log_15629_neg
  have he : Real.log (262657894736843 / 500000000000) = -Real.log (500000000000 / 262657894736843) := by
    rw [show ((262657894736843 / 500000000000) : ℝ) = ((500000000000 / 262657894736843) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15630_neg : (345672779 / 500000000) ≤ -Real.log (2500 / 4991) ∧
    -Real.log (2500 / 4991) ≤ (691345559 / 1000000000) := by
  have h := checkLog_sound (w := (2491 / 7491)) (n := 12)
    (lo := (345672779 / 500000000)) (hi := (691345559 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4991 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4991 / 2500) = 1/(2500 / 4991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15630 : Bounds (345672779 / 500000000) (691345559 / 1000000000) (Real.log (4991 / 2500)) := by
  have h := reflection_log_15630_neg
  have he : Real.log (4991 / 2500) = -Real.log (2500 / 4991) := by
    rw [show ((4991 / 2500) : ℝ) = ((2500 / 4991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15631_neg : (5626821429 / 1000000000) ≤ -Real.log (9 / 2500) ∧
    -Real.log (9 / 2500) ≤ (2813410719 / 500000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 576) = 1/(9 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15631 : Bounds (-2813410719 / 500000000) (-5626821429 / 1000000000) (Real.log (9 / 2500)) := by
  have h := reflection_log_15631_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15632_neg : (995903 / 1000000000) ≤ -Real.log (2500000 / 2502491) ∧
    -Real.log (2500000 / 2502491) ≤ (15561 / 15625000) := by
  have h := checkLog_sound (w := (2491 / 5002491)) (n := 12)
    (lo := (995903 / 1000000000)) (hi := (15561 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502491 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502491 / 2500000) = 1/(2500000 / 2502491) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15632 : Bounds (995903 / 1000000000) (15561 / 15625000) (Real.log (2502491 / 2500000)) := by
  have h := reflection_log_15632_neg
  have he : Real.log (2502491 / 2500000) = -Real.log (2500000 / 2502491) := by
    rw [show ((2502491 / 2500000) : ℝ) = ((2500000 / 2502491) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15633_neg : (31153 / 31250000) ≤ -Real.log (2497509 / 2500000) ∧
    -Real.log (2497509 / 2500000) ≤ (996897 / 1000000000) := by
  have h := checkLog_sound (w := (2491 / 4997509)) (n := 12)
    (lo := (31153 / 31250000)) (hi := (996897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497509) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497509) = 1/(2497509 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15633 : Bounds (-996897 / 1000000000) (-31153 / 31250000) (Real.log (2497509 / 2500000)) := by
  have h := reflection_log_15633_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15634_neg : (100317537 / 200000000) ≤ -Real.log (1000000 / 1651341) ∧
    -Real.log (1000000 / 1651341) ≤ (250793843 / 500000000) := by
  have h := checkLog_sound (w := (651341 / 2651341)) (n := 12)
    (lo := (100317537 / 200000000)) (hi := (250793843 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1651341 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1651341 / 1000000) = 1/(1000000 / 1651341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15634 : Bounds (100317537 / 200000000) (250793843 / 500000000) (Real.log (1651341 / 1000000)) := by
  have h := reflection_log_15634_neg
  have he : Real.log (1651341 / 1000000) = -Real.log (1000000 / 1651341) := by
    rw [show ((1651341 / 1000000) : ℝ) = ((1000000 / 1651341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15635_neg : (1053660911 / 1000000000) ≤ -Real.log (348659 / 1000000) ∧
    -Real.log (348659 / 1000000) ≤ (1053660913 / 1000000000) := by
  have h := checkLog_sound (w := (151341 / 848659)) (n := 12)
    (lo := (360513731 / 1000000000)) (hi := (90128433 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 348659) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 348659) = 1/(348659 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15635 : Bounds (-1053660913 / 1000000000) (-1053660911 / 1000000000) (Real.log (348659 / 1000000)) := by
  have h := reflection_log_15635_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15636_neg : (502169467 / 1000000000) ≤ -Real.log (500000 / 826151) ∧
    -Real.log (500000 / 826151) ≤ (125542367 / 250000000) := by
  have h := checkLog_sound (w := (326151 / 1326151)) (n := 12)
    (lo := (502169467 / 1000000000)) (hi := (125542367 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826151 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826151 / 500000) = 1/(500000 / 826151) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15636 : Bounds (502169467 / 1000000000) (125542367 / 250000000) (Real.log (826151 / 500000)) := by
  have h := reflection_log_15636_neg
  have he : Real.log (826151 / 500000) = -Real.log (500000 / 826151) := by
    rw [show ((826151 / 500000) : ℝ) = ((500000 / 826151) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15637_neg : (1056420991 / 1000000000) ≤ -Real.log (173849 / 500000) ∧
    -Real.log (173849 / 500000) ≤ (1056420993 / 1000000000) := by
  have h := checkLog_sound (w := (76151 / 423849)) (n := 12)
    (lo := (363273811 / 1000000000)) (hi := (90818453 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173849) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173849) = 1/(173849 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15637 : Bounds (-1056420993 / 1000000000) (-1056420991 / 1000000000) (Real.log (173849 / 500000)) := by
  have h := reflection_log_15637_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15638_neg : (138562881 / 250000000) ≤ -Real.log (143625525199 / 250000000000) ∧
    -Real.log (143625525199 / 250000000000) ≤ (22170061 / 40000000) := by
  have h := checkLog_sound (w := (106374474801 / 393625525199)) (n := 12)
    (lo := (138562881 / 250000000)) (hi := (22170061 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143625525199) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143625525199) = 1/(143625525199 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15638 : Bounds (-22170061 / 40000000) (-138562881 / 250000000) (Real.log (143625525199 / 250000000000)) := by
  have h := reflection_log_15638_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15639_neg : (276036613 / 500000000) ≤ -Real.log (575754901719 / 1000000000000) ∧
    -Real.log (575754901719 / 1000000000000) ≤ (552073227 / 1000000000) := by
  have h := checkLog_sound (w := (424245098281 / 1575754901719)) (n := 12)
    (lo := (276036613 / 500000000)) (hi := (552073227 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 575754901719) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 575754901719) = 1/(575754901719 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15639 : Bounds (-552073227 / 1000000000) (-276036613 / 500000000) (Real.log (575754901719 / 1000000000000)) := by
  have h := reflection_log_15639_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15640_neg : (311049719 / 200000000) ≤ -Real.log (500000000000 / 2368131899649) ∧
    -Real.log (500000000000 / 2368131899649) ≤ (777624299 / 500000000) := by
  have h := checkLog_sound (w := (368131899649 / 4368131899649)) (n := 12)
    (lo := (33790847 / 200000000)) (hi := (42238559 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2368131899649 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2368131899649 / 2000000000000) = 1/(500000000000 / 2368131899649) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15640 : Bounds (311049719 / 200000000) (777624299 / 500000000) (Real.log (2368131899649 / 500000000000)) := by
  have h := reflection_log_15640_neg
  have he : Real.log (2368131899649 / 500000000000) = -Real.log (500000000000 / 2368131899649) := by
    rw [show ((2368131899649 / 500000000000) : ℝ) = ((500000000000 / 2368131899649) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15641_neg : (779295229 / 500000000) ≤ -Real.log (500000000000 / 2376059108767) ∧
    -Real.log (500000000000 / 2376059108767) ≤ (1558590461 / 1000000000) := by
  have h := checkLog_sound (w := (376059108767 / 4376059108767)) (n := 12)
    (lo := (86148049 / 500000000)) (hi := (172296099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2376059108767 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2376059108767 / 2000000000000) = 1/(500000000000 / 2376059108767) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15641 : Bounds (779295229 / 500000000) (1558590461 / 1000000000) (Real.log (2376059108767 / 500000000000)) := by
  have h := reflection_log_15641_neg
  have he : Real.log (2376059108767 / 500000000000) = -Real.log (500000000000 / 2376059108767) := by
    rw [show ((2376059108767 / 500000000000) : ℝ) = ((500000000000 / 2376059108767) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15642_neg : (313199979 / 50000000) ≤ -Real.log (250000000000 / 131328947368421) ∧
    -Real.log (250000000000 / 131328947368421) ≤ (626399959 / 100000000) := by
  have h := checkLog_sound (w := (3328947368421 / 259328947368421)) (n := 12)
    (lo := (320937 / 12500000)) (hi := (25674961 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((131328947368421 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(131328947368421 / 128000000000000) = 1/(250000000000 / 131328947368421) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15642 : Bounds (313199979 / 50000000) (626399959 / 100000000) (Real.log (131328947368421 / 250000000000)) := by
  have h := reflection_log_15642_neg
  have he : Real.log (131328947368421 / 250000000000) = -Real.log (250000000000 / 131328947368421) := by
    rw [show ((131328947368421 / 250000000000) : ℝ) = ((250000000000 / 131328947368421) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15643_neg : (6318166987 / 1000000000) ≤ -Real.log (250000000000 / 138638888888889) ∧
    -Real.log (250000000000 / 138638888888889) ≤ (6318166997 / 1000000000) := by
  have h := checkLog_sound (w := (10638888888889 / 266638888888889)) (n := 12)
    (lo := (79842367 / 1000000000)) (hi := (1247537 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138638888888889 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(138638888888889 / 128000000000000) = 1/(250000000000 / 138638888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15643 : Bounds (6318166987 / 1000000000) (6318166997 / 1000000000) (Real.log (138638888888889 / 250000000000)) := by
  have h := reflection_log_15643_neg
  have he : Real.log (138638888888889 / 250000000000) = -Real.log (250000000000 / 138638888888889) := by
    rw [show ((138638888888889 / 250000000000) : ℝ) = ((250000000000 / 138638888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15644_neg : (691445733 / 1000000000) ≤ -Real.log (5000 / 9983) ∧
    -Real.log (5000 / 9983) ≤ (345722867 / 500000000) := by
  have h := checkLog_sound (w := (4983 / 14983)) (n := 12)
    (lo := (691445733 / 1000000000)) (hi := (345722867 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9983 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9983 / 5000) = 1/(5000 / 9983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15644 : Bounds (691445733 / 1000000000) (345722867 / 500000000) (Real.log (9983 / 5000)) := by
  have h := reflection_log_15644_neg
  have he : Real.log (9983 / 5000) = -Real.log (5000 / 9983) := by
    rw [show ((9983 / 5000) : ℝ) = ((5000 / 9983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15645_neg : (2841989921 / 500000000) ≤ -Real.log (17 / 5000) ∧
    -Real.log (17 / 5000) ≤ (5683979851 / 1000000000) := by
  have h := checkLog_sound (w := (81 / 1169)) (n := 12)
    (lo := (69401201 / 500000000)) (hi := (138802403 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 544) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 544) = 1/(17 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15645 : Bounds (-5683979851 / 1000000000) (-2841989921 / 500000000) (Real.log (17 / 5000)) := by
  have h := reflection_log_15645_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15646_neg : (996103 / 1000000000) ≤ -Real.log (5000000 / 5004983) ∧
    -Real.log (5000000 / 5004983) ≤ (124513 / 125000000) := by
  have h := checkLog_sound (w := (4983 / 10004983)) (n := 12)
    (lo := (996103 / 1000000000)) (hi := (124513 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004983 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004983 / 5000000) = 1/(5000000 / 5004983) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15646 : Bounds (996103 / 1000000000) (124513 / 125000000) (Real.log (5004983 / 5000000)) := by
  have h := reflection_log_15646_neg
  have he : Real.log (5004983 / 5000000) = -Real.log (5000000 / 5004983) := by
    rw [show ((5004983 / 5000000) : ℝ) = ((5000000 / 5004983) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15647_neg : (124637 / 125000000) ≤ -Real.log (4995017 / 5000000) ∧
    -Real.log (4995017 / 5000000) ≤ (997097 / 1000000000) := by
  have h := checkLog_sound (w := (4983 / 9995017)) (n := 12)
    (lo := (124637 / 125000000)) (hi := (997097 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995017) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995017) = 1/(4995017 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15647 : Bounds (-997097 / 1000000000) (-124637 / 125000000) (Real.log (4995017 / 5000000)) := by
  have h := reflection_log_15647_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15648_neg : (501792951 / 1000000000) ≤ -Real.log (6250 / 10323) ∧
    -Real.log (6250 / 10323) ≤ (62724119 / 125000000) := by
  have h := checkLog_sound (w := (4073 / 16573)) (n := 12)
    (lo := (501792951 / 1000000000)) (hi := (62724119 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((10323 / 6250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(10323 / 6250) = 1/(6250 / 10323) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15648 : Bounds (501792951 / 1000000000) (62724119 / 125000000) (Real.log (10323 / 6250)) := by
  have h := reflection_log_15648_neg
  have he : Real.log (10323 / 6250) = -Real.log (6250 / 10323) := by
    rw [show ((10323 / 6250) : ℝ) = ((6250 / 10323) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15649_neg : (13182921 / 12500000) ≤ -Real.log (2177 / 6250) ∧
    -Real.log (2177 / 6250) ≤ (527316841 / 500000000) := by
  have h := checkLog_sound (w := (474 / 2651)) (n := 12)
    (lo := (722973 / 2000000)) (hi := (361486501 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3125 / 2177) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(3125 / 2177) = 1/(2177 / 6250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15649 : Bounds (-527316841 / 500000000) (-13182921 / 12500000) (Real.log (2177 / 6250)) := by
  have h := reflection_log_15649_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15650_neg : (502376429 / 1000000000) ≤ -Real.log (250000 / 413161) ∧
    -Real.log (250000 / 413161) ≤ (50237643 / 100000000) := by
  have h := checkLog_sound (w := (163161 / 663161)) (n := 12)
    (lo := (502376429 / 1000000000)) (hi := (50237643 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413161 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413161 / 250000) = 1/(250000 / 413161) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15650 : Bounds (502376429 / 1000000000) (50237643 / 100000000) (Real.log (413161 / 250000)) := by
  have h := reflection_log_15650_neg
  have he : Real.log (413161 / 250000) = -Real.log (250000 / 413161) := by
    rw [show ((413161 / 250000) : ℝ) = ((250000 / 413161) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15651_neg : (1057405087 / 1000000000) ≤ -Real.log (86839 / 250000) ∧
    -Real.log (86839 / 250000) ≤ (1057405089 / 1000000000) := by
  have h := checkLog_sound (w := (38161 / 211839)) (n := 12)
    (lo := (364257907 / 1000000000)) (hi := (91064477 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86839) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86839) = 1/(86839 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15651 : Bounds (-1057405089 / 1000000000) (-1057405087 / 1000000000) (Real.log (86839 / 250000)) := by
  have h := reflection_log_15651_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15652_neg : (277514329 / 500000000) ≤ -Real.log (35878488079 / 62500000000) ∧
    -Real.log (35878488079 / 62500000000) ≤ (555028659 / 1000000000) := by
  have h := checkLog_sound (w := (26621511921 / 98378488079)) (n := 12)
    (lo := (277514329 / 500000000)) (hi := (555028659 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35878488079) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35878488079) = 1/(35878488079 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15652 : Bounds (-555028659 / 1000000000) (-277514329 / 500000000) (Real.log (35878488079 / 62500000000)) := by
  have h := reflection_log_15652_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15653_neg : (552840729 / 1000000000) ≤ -Real.log (22473171 / 39062500) ∧
    -Real.log (22473171 / 39062500) ≤ (55284073 / 100000000) := by
  have h := checkLog_sound (w := (16589329 / 61535671)) (n := 12)
    (lo := (552840729 / 1000000000)) (hi := (55284073 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39062500 / 22473171) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(39062500 / 22473171) = 1/(22473171 / 39062500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15653 : Bounds (-55284073 / 100000000) (-552840729 / 1000000000) (Real.log (22473171 / 39062500)) := by
  have h := reflection_log_15653_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15654_neg : (194553329 / 125000000) ≤ -Real.log (500000000000 / 2370923288929) ∧
    -Real.log (500000000000 / 2370923288929) ≤ (311285327 / 200000000) := by
  have h := checkLog_sound (w := (370923288929 / 4370923288929)) (n := 12)
    (lo := (10633267 / 62500000)) (hi := (170132273 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2370923288929 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2370923288929 / 2000000000000) = 1/(500000000000 / 2370923288929) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15654 : Bounds (194553329 / 125000000) (311285327 / 200000000) (Real.log (2370923288929 / 500000000000)) := by
  have h := reflection_log_15654_neg
  have he : Real.log (2370923288929 / 500000000000) = -Real.log (500000000000 / 2370923288929) := by
    rw [show ((2370923288929 / 500000000000) : ℝ) = ((500000000000 / 2370923288929) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15655_neg : (389945379 / 250000000) ≤ -Real.log (100000000000 / 475778164189) ∧
    -Real.log (100000000000 / 475778164189) ≤ (1559781519 / 1000000000) := by
  have h := checkLog_sound (w := (75778164189 / 875778164189)) (n := 12)
    (lo := (43371789 / 250000000)) (hi := (173487157 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((475778164189 / 400000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(475778164189 / 400000000000) = 1/(100000000000 / 475778164189) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15655 : Bounds (389945379 / 250000000) (1559781519 / 1000000000) (Real.log (475778164189 / 100000000000)) := by
  have h := reflection_log_15655_neg
  have he : Real.log (475778164189 / 100000000000) = -Real.log (100000000000 / 475778164189) := by
    rw [show ((475778164189 / 100000000000) : ℝ) = ((100000000000 / 475778164189) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15656_neg : (6318166987 / 1000000000) ≤ -Real.log (500000000000 / 277277777777777) ∧
    -Real.log (500000000000 / 277277777777777) ≤ (6318166997 / 1000000000) := by
  have h := checkLog_sound (w := (21277777777777 / 533277777777777)) (n := 12)
    (lo := (79842367 / 1000000000)) (hi := (1247537 / 15625000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((277277777777777 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(277277777777777 / 256000000000000) = 1/(500000000000 / 277277777777777) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15656 : Bounds (6318166987 / 1000000000) (6318166997 / 1000000000) (Real.log (277277777777777 / 500000000000)) := by
  have h := reflection_log_15656_neg
  have he : Real.log (277277777777777 / 500000000000) = -Real.log (500000000000 / 277277777777777) := by
    rw [show ((277277777777777 / 500000000000) : ℝ) = ((500000000000 / 277277777777777) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15657_neg : (796928197 / 125000000) ≤ -Real.log (62500000000 / 36702205882353) ∧
    -Real.log (62500000000 / 36702205882353) ≤ (3187712793 / 500000000) := by
  have h := checkLog_sound (w := (4702205882353 / 68702205882353)) (n := 12)
    (lo := (34275239 / 250000000)) (hi := (137100957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((36702205882353 / 32000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(36702205882353 / 32000000000000) = 1/(62500000000 / 36702205882353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15657 : Bounds (796928197 / 125000000) (3187712793 / 500000000) (Real.log (36702205882353 / 62500000000)) := by
  have h := reflection_log_15657_neg
  have he : Real.log (36702205882353 / 62500000000) = -Real.log (62500000000 / 36702205882353) := by
    rw [show ((36702205882353 / 62500000000) : ℝ) = ((62500000000 / 36702205882353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15658_neg : (691545899 / 1000000000) ≤ -Real.log (625 / 1248) ∧
    -Real.log (625 / 1248) ≤ (6915459 / 10000000) := by
  have h := checkLog_sound (w := (623 / 1873)) (n := 12)
    (lo := (691545899 / 1000000000)) (hi := (6915459 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1248 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1248 / 625) = 1/(625 / 1248) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15658 : Bounds (691545899 / 1000000000) (6915459 / 10000000) (Real.log (1248 / 625)) := by
  have h := reflection_log_15658_neg
  have he : Real.log (1248 / 625) = -Real.log (625 / 1248) := by
    rw [show ((1248 / 625) : ℝ) = ((625 / 1248) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15659_neg : (359037779 / 62500000) ≤ -Real.log (2 / 625) ∧
    -Real.log (2 / 625) ≤ (5744604473 / 1000000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 512) = 1/(2 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15659 : Bounds (-5744604473 / 1000000000) (-359037779 / 62500000) (Real.log (2 / 625)) := by
  have h := reflection_log_15659_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15660_neg : (996303 / 1000000000) ≤ -Real.log (625000 / 625623) ∧
    -Real.log (625000 / 625623) ≤ (62269 / 62500000) := by
  have h := checkLog_sound (w := (623 / 1250623)) (n := 12)
    (lo := (996303 / 1000000000)) (hi := (62269 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625623 / 625000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625623 / 625000) = 1/(625000 / 625623) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15660 : Bounds (996303 / 1000000000) (62269 / 62500000) (Real.log (625623 / 625000)) := by
  have h := reflection_log_15660_neg
  have he : Real.log (625623 / 625000) = -Real.log (625000 / 625623) := by
    rw [show ((625623 / 625000) : ℝ) = ((625000 / 625623) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15661_neg : (997297 / 1000000000) ≤ -Real.log (624377 / 625000) ∧
    -Real.log (624377 / 625000) ≤ (498649 / 500000000) := by
  have h := checkLog_sound (w := (623 / 1249377)) (n := 12)
    (lo := (997297 / 1000000000)) (hi := (498649 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625000 / 624377) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(625000 / 624377) = 1/(624377 / 625000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15661 : Bounds (-498649 / 500000000) (-997297 / 1000000000) (Real.log (624377 / 625000)) := by
  have h := reflection_log_15661_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15662_neg : (250999693 / 500000000) ≤ -Real.log (1000000 / 1652021) ∧
    -Real.log (1000000 / 1652021) ≤ (501999387 / 1000000000) := by
  have h := checkLog_sound (w := (652021 / 2652021)) (n := 12)
    (lo := (250999693 / 500000000)) (hi := (501999387 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1652021 / 1000000) = 1/(1000000 / 1652021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15662 : Bounds (250999693 / 500000000) (501999387 / 1000000000) (Real.log (1652021 / 1000000)) := by
  have h := reflection_log_15662_neg
  have he : Real.log (1652021 / 1000000) = -Real.log (1000000 / 1652021) := by
    rw [show ((1652021 / 1000000) : ℝ) = ((1000000 / 1652021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15663_neg : (211122629 / 200000000) ≤ -Real.log (347979 / 1000000) ∧
    -Real.log (347979 / 1000000) ≤ (1055613147 / 1000000000) := by
  have h := checkLog_sound (w := (152021 / 847979)) (n := 12)
    (lo := (72493193 / 200000000)) (hi := (181232983 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347979) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 347979) = 1/(347979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15663 : Bounds (-1055613147 / 1000000000) (-211122629 / 200000000) (Real.log (347979 / 1000000)) := by
  have h := reflection_log_15663_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15664_neg : (502584559 / 1000000000) ≤ -Real.log (250000 / 413247) ∧
    -Real.log (250000 / 413247) ≤ (6282307 / 12500000) := by
  have h := checkLog_sound (w := (163247 / 663247)) (n := 12)
    (lo := (502584559 / 1000000000)) (hi := (6282307 / 12500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413247 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413247 / 250000) = 1/(250000 / 413247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15664 : Bounds (502584559 / 1000000000) (6282307 / 12500000) (Real.log (413247 / 250000)) := by
  have h := reflection_log_15664_neg
  have he : Real.log (413247 / 250000) = -Real.log (250000 / 413247) := by
    rw [show ((413247 / 250000) : ℝ) = ((250000 / 413247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15665_neg : (264598979 / 250000000) ≤ -Real.log (86753 / 250000) ∧
    -Real.log (86753 / 250000) ≤ (529197959 / 500000000) := by
  have h := checkLog_sound (w := (38247 / 211753)) (n := 12)
    (lo := (11414023 / 31250000)) (hi := (365248737 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86753) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86753) = 1/(86753 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15665 : Bounds (-529197959 / 500000000) (-264598979 / 250000000) (Real.log (86753 / 250000)) := by
  have h := reflection_log_15665_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15666_neg : (277905679 / 500000000) ≤ -Real.log (35850416991 / 62500000000) ∧
    -Real.log (35850416991 / 62500000000) ≤ (555811359 / 1000000000) := by
  have h := checkLog_sound (w := (26649583009 / 98350416991)) (n := 12)
    (lo := (277905679 / 500000000)) (hi := (555811359 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35850416991) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35850416991) = 1/(35850416991 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15666 : Bounds (-555811359 / 1000000000) (-277905679 / 500000000) (Real.log (35850416991 / 62500000000)) := by
  have h := reflection_log_15666_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15667_neg : (276806879 / 500000000) ≤ -Real.log (574868615559 / 1000000000000) ∧
    -Real.log (574868615559 / 1000000000000) ≤ (553613759 / 1000000000) := by
  have h := checkLog_sound (w := (425131384441 / 1574868615559)) (n := 12)
    (lo := (276806879 / 500000000)) (hi := (553613759 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 574868615559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 574868615559) = 1/(574868615559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15667 : Bounds (-553613759 / 1000000000) (-276806879 / 500000000) (Real.log (574868615559 / 1000000000000)) := by
  have h := reflection_log_15667_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15668_neg : (1557612531 / 1000000000) ≤ -Real.log (125000000000 / 593434158383) ∧
    -Real.log (125000000000 / 593434158383) ≤ (778806267 / 500000000) := by
  have h := checkLog_sound (w := (93434158383 / 1093434158383)) (n := 12)
    (lo := (171318171 / 1000000000)) (hi := (42829543 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((593434158383 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(593434158383 / 500000000000) = 1/(125000000000 / 593434158383) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15668 : Bounds (1557612531 / 1000000000) (778806267 / 500000000) (Real.log (593434158383 / 125000000000)) := by
  have h := reflection_log_15668_neg
  have he : Real.log (593434158383 / 125000000000) = -Real.log (125000000000 / 593434158383) := by
    rw [show ((593434158383 / 125000000000) : ℝ) = ((125000000000 / 593434158383) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15669_neg : (62439219 / 40000000) ≤ -Real.log (250000000000 / 1190872361763) ∧
    -Real.log (250000000000 / 1190872361763) ≤ (780490239 / 500000000) := by
  have h := checkLog_sound (w := (190872361763 / 2190872361763)) (n := 12)
    (lo := (34937223 / 200000000)) (hi := (43671529 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1190872361763 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1190872361763 / 1000000000000) = 1/(250000000000 / 1190872361763) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15669 : Bounds (62439219 / 40000000) (780490239 / 500000000) (Real.log (1190872361763 / 250000000000)) := by
  have h := reflection_log_15669_neg
  have he : Real.log (1190872361763 / 250000000000) = -Real.log (250000000000 / 1190872361763) := by
    rw [show ((1190872361763 / 250000000000) : ℝ) = ((250000000000 / 1190872361763) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15670_neg : (796928197 / 125000000) ≤ -Real.log (500000000000 / 293617647058823) ∧
    -Real.log (500000000000 / 293617647058823) ≤ (3187712793 / 500000000) := by
  have h := checkLog_sound (w := (37617647058823 / 549617647058823)) (n := 12)
    (lo := (34275239 / 250000000)) (hi := (137100957 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((293617647058823 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(293617647058823 / 256000000000000) = 1/(500000000000 / 293617647058823) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15670 : Bounds (796928197 / 125000000) (3187712793 / 500000000) (Real.log (293617647058823 / 500000000000)) := by
  have h := reflection_log_15670_neg
  have he : Real.log (293617647058823 / 500000000000) = -Real.log (500000000000 / 293617647058823) := by
    rw [show ((293617647058823 / 500000000000) : ℝ) = ((500000000000 / 293617647058823) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15671_neg : (6436150363 / 1000000000) ≤ -Real.log (1 / 624) ∧
    -Real.log (1 / 624) ≤ (6436150373 / 1000000000) := by
  have h := checkLog_sound (w := (7 / 71)) (n := 12)
    (lo := (197825743 / 1000000000)) (hi := (12364109 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((39 / 32) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(39 / 32) = 1/(1 / 624) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15671 : Bounds (6436150363 / 1000000000) (6436150373 / 1000000000) (Real.log (624 / 1)) := by
  have h := reflection_log_15671_neg
  have he : Real.log (624 / 1) = -Real.log (1 / 624) := by
    rw [show ((624 / 1) : ℝ) = ((1 / 624) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15672_neg : (345823027 / 500000000) ≤ -Real.log (1000 / 1997) ∧
    -Real.log (1000 / 1997) ≤ (138329211 / 200000000) := by
  have h := checkLog_sound (w := (997 / 2997)) (n := 12)
    (lo := (345823027 / 500000000)) (hi := (138329211 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1997 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1997 / 1000) = 1/(1000 / 1997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15672 : Bounds (345823027 / 500000000) (138329211 / 200000000) (Real.log (1997 / 1000)) := by
  have h := reflection_log_15672_neg
  have he : Real.log (1997 / 1000) = -Real.log (1000 / 1997) := by
    rw [show ((1997 / 1000) : ℝ) = ((1000 / 1997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15673_neg : (1161828597 / 200000000) ≤ -Real.log (3 / 1000) ∧
    -Real.log (3 / 1000) ≤ (2904571497 / 500000000) := by
  have h := checkLog_sound (w := (29 / 221)) (n := 12)
    (lo := (52793109 / 200000000)) (hi := (131982773 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 96) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(125 / 96) = 1/(3 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15673 : Bounds (-2904571497 / 500000000) (-1161828597 / 200000000) (Real.log (3 / 1000)) := by
  have h := reflection_log_15673_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15674_neg : (996503 / 1000000000) ≤ -Real.log (1000000 / 1000997) ∧
    -Real.log (1000000 / 1000997) ≤ (124563 / 125000000) := by
  have h := checkLog_sound (w := (997 / 2000997)) (n := 12)
    (lo := (996503 / 1000000000)) (hi := (124563 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000997 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000997 / 1000000) = 1/(1000000 / 1000997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15674 : Bounds (996503 / 1000000000) (124563 / 125000000) (Real.log (1000997 / 1000000)) := by
  have h := reflection_log_15674_neg
  have he : Real.log (1000997 / 1000000) = -Real.log (1000000 / 1000997) := by
    rw [show ((1000997 / 1000000) : ℝ) = ((1000000 / 1000997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15675_neg : (997497 / 1000000000) ≤ -Real.log (999003 / 1000000) ∧
    -Real.log (999003 / 1000000) ≤ (498749 / 500000000) := by
  have h := checkLog_sound (w := (997 / 1999003)) (n := 12)
    (lo := (997497 / 1000000000)) (hi := (498749 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999003) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999003) = 1/(999003 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15675 : Bounds (-498749 / 500000000) (-997497 / 1000000000) (Real.log (999003 / 1000000)) := by
  have h := reflection_log_15675_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15676_neg : (2511041 / 5000000) ≤ -Real.log (500000 / 826183) ∧
    -Real.log (500000 / 826183) ≤ (502208201 / 1000000000) := by
  have h := checkLog_sound (w := (326183 / 1326183)) (n := 12)
    (lo := (2511041 / 5000000)) (hi := (502208201 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826183 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826183 / 500000) = 1/(500000 / 826183) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15676 : Bounds (2511041 / 5000000) (502208201 / 1000000000) (Real.log (826183 / 500000)) := by
  have h := reflection_log_15676_neg
  have he : Real.log (826183 / 500000) = -Real.log (500000 / 826183) := by
    rw [show ((826183 / 500000) : ℝ) = ((500000 / 826183) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15677_neg : (264151269 / 250000000) ≤ -Real.log (173817 / 500000) ∧
    -Real.log (173817 / 500000) ≤ (528302539 / 500000000) := by
  have h := checkLog_sound (w := (76183 / 423817)) (n := 12)
    (lo := (45432237 / 125000000)) (hi := (363457897 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173817) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173817) = 1/(173817 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15677 : Bounds (-528302539 / 500000000) (-264151269 / 250000000) (Real.log (173817 / 500000)) := by
  have h := reflection_log_15677_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15678_neg : (25139723 / 50000000) ≤ -Real.log (200000 / 330667) ∧
    -Real.log (200000 / 330667) ≤ (502794461 / 1000000000) := by
  have h := checkLog_sound (w := (130667 / 530667)) (n := 12)
    (lo := (25139723 / 50000000)) (hi := (502794461 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330667 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330667 / 200000) = 1/(200000 / 330667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15678 : Bounds (25139723 / 50000000) (502794461 / 1000000000) (Real.log (330667 / 200000)) := by
  have h := reflection_log_15678_neg
  have he : Real.log (330667 / 200000) = -Real.log (200000 / 330667) := by
    rw [show ((330667 / 200000) : ℝ) = ((200000 / 330667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15679_neg : (529698191 / 500000000) ≤ -Real.log (69333 / 200000) ∧
    -Real.log (69333 / 200000) ≤ (33106137 / 31250000) := by
  have h := checkLog_sound (w := (30667 / 169333)) (n := 12)
    (lo := (183124601 / 500000000)) (hi := (366249203 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69333) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69333) = 1/(69333 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15679 : Bounds (-33106137 / 31250000) (-529698191 / 500000000) (Real.log (69333 / 200000)) := by
  have h := reflection_log_15679_neg
  constructor <;> linarith [h.1,h.2]

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0245 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15680_neg : (556601923 / 1000000000) ≤ -Real.log (22926135111 / 40000000000) ∧
    -Real.log (22926135111 / 40000000000) ≤ (139150481 / 250000000) := by
  have h := checkLog_sound (w := (17073864889 / 62926135111)) (n := 12)
    (lo := (556601923 / 1000000000)) (hi := (139150481 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22926135111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22926135111) = 1/(22926135111 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15680 : Bounds (-139150481 / 250000000) (-556601923 / 1000000000) (Real.log (22926135111 / 40000000000)) := by
  have h := reflection_log_15680_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15681_neg : (138599219 / 250000000) ≤ -Real.log (143604650511 / 250000000000) ∧
    -Real.log (143604650511 / 250000000000) ≤ (554396877 / 1000000000) := by
  have h := checkLog_sound (w := (106395349489 / 393604650511)) (n := 12)
    (lo := (138599219 / 250000000)) (hi := (554396877 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143604650511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143604650511) = 1/(143604650511 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15681 : Bounds (-554396877 / 1000000000) (-138599219 / 250000000) (Real.log (143604650511 / 250000000000)) := by
  have h := reflection_log_15681_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15682_neg : (62352531 / 40000000) ≤ -Real.log (125000000000 / 594147149013) ∧
    -Real.log (125000000000 / 594147149013) ≤ (779406639 / 500000000) := by
  have h := checkLog_sound (w := (94147149013 / 1094147149013)) (n := 12)
    (lo := (34503783 / 200000000)) (hi := (43129729 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((594147149013 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(594147149013 / 500000000000) = 1/(125000000000 / 594147149013) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15682 : Bounds (62352531 / 40000000) (779406639 / 500000000) (Real.log (594147149013 / 125000000000)) := by
  have h := reflection_log_15682_neg
  have he : Real.log (594147149013 / 125000000000) = -Real.log (125000000000 / 594147149013) := by
    rw [show ((594147149013 / 125000000000) : ℝ) = ((125000000000 / 594147149013) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15683_neg : (781095421 / 500000000) ≤ -Real.log (250000000000 / 1192314626513) ∧
    -Real.log (250000000000 / 1192314626513) ≤ (312438169 / 200000000) := by
  have h := checkLog_sound (w := (192314626513 / 2192314626513)) (n := 12)
    (lo := (87948241 / 500000000)) (hi := (175896483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1192314626513 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1192314626513 / 1000000000000) = 1/(250000000000 / 1192314626513) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15683 : Bounds (781095421 / 500000000) (312438169 / 200000000) (Real.log (1192314626513 / 250000000000)) := by
  have h := reflection_log_15683_neg
  have he : Real.log (1192314626513 / 250000000000) = -Real.log (250000000000 / 1192314626513) := by
    rw [show ((1192314626513 / 250000000000) : ℝ) = ((250000000000 / 1192314626513) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15684_neg : (6500789039 / 1000000000) ≤ -Real.log (250000000000 / 166416666666667) ∧
    -Real.log (250000000000 / 166416666666667) ≤ (6500789049 / 1000000000) := by
  have h := checkLog_sound (w := (38416666666667 / 294416666666667)) (n := 12)
    (lo := (262464419 / 1000000000)) (hi := (13123221 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((166416666666667 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(166416666666667 / 128000000000000) = 1/(250000000000 / 166416666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15684 : Bounds (6500789039 / 1000000000) (6500789049 / 1000000000) (Real.log (166416666666667 / 250000000000)) := by
  have h := reflection_log_15684_neg
  have he : Real.log (166416666666667 / 250000000000) = -Real.log (250000000000 / 166416666666667) := by
    rw [show ((166416666666667 / 250000000000) : ℝ) = ((250000000000 / 166416666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15685_neg : (691746199 / 1000000000) ≤ -Real.log (2500 / 4993) ∧
    -Real.log (2500 / 4993) ≤ (3458731 / 5000000) := by
  have h := checkLog_sound (w := (2493 / 7493)) (n := 12)
    (lo := (691746199 / 1000000000)) (hi := (3458731 / 5000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4993 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4993 / 2500) = 1/(2500 / 4993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15685 : Bounds (691746199 / 1000000000) (3458731 / 5000000) (Real.log (4993 / 2500)) := by
  have h := reflection_log_15685_neg
  have he : Real.log (4993 / 2500) = -Real.log (2500 / 4993) := by
    rw [show ((4993 / 2500) : ℝ) = ((2500 / 4993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15686_neg : (5878135857 / 1000000000) ≤ -Real.log (7 / 2500) ∧
    -Real.log (7 / 2500) ≤ (2939067933 / 500000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 448) = 1/(7 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15686 : Bounds (-2939067933 / 500000000) (-5878135857 / 1000000000) (Real.log (7 / 2500)) := by
  have h := reflection_log_15686_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15687_neg : (996703 / 1000000000) ≤ -Real.log (2500000 / 2502493) ∧
    -Real.log (2500000 / 2502493) ≤ (31147 / 31250000) := by
  have h := checkLog_sound (w := (2493 / 5002493)) (n := 12)
    (lo := (996703 / 1000000000)) (hi := (31147 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502493 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502493 / 2500000) = 1/(2500000 / 2502493) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15687 : Bounds (996703 / 1000000000) (31147 / 31250000) (Real.log (2502493 / 2500000)) := by
  have h := reflection_log_15687_neg
  have he : Real.log (2502493 / 2500000) = -Real.log (2500000 / 2502493) := by
    rw [show ((2502493 / 2500000) : ℝ) = ((2500000 / 2502493) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15688_neg : (997697 / 1000000000) ≤ -Real.log (2497507 / 2500000) ∧
    -Real.log (2497507 / 2500000) ≤ (498849 / 500000000) := by
  have h := checkLog_sound (w := (2493 / 4997507)) (n := 12)
    (lo := (997697 / 1000000000)) (hi := (498849 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497507) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497507) = 1/(2497507 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15688 : Bounds (-498849 / 500000000) (-997697 / 1000000000) (Real.log (2497507 / 2500000)) := by
  have h := reflection_log_15688_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15689_neg : (25120909 / 50000000) ≤ -Real.log (1000000 / 1652713) ∧
    -Real.log (1000000 / 1652713) ≤ (502418181 / 1000000000) := by
  have h := checkLog_sound (w := (652713 / 2652713)) (n := 12)
    (lo := (25120909 / 50000000)) (hi := (502418181 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1652713 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1652713 / 1000000) = 1/(1000000 / 1652713) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15689 : Bounds (25120909 / 50000000) (502418181 / 1000000000) (Real.log (1652713 / 1000000)) := by
  have h := reflection_log_15689_neg
  have he : Real.log (1652713 / 1000000) = -Real.log (1000000 / 1652713) := by
    rw [show ((1652713 / 1000000) : ℝ) = ((1000000 / 1652713) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15690_neg : (846083 / 800000) ≤ -Real.log (347287 / 1000000) ∧
    -Real.log (347287 / 1000000) ≤ (132200469 / 125000000) := by
  have h := checkLog_sound (w := (152713 / 847287)) (n := 12)
    (lo := (36445657 / 100000000)) (hi := (364456571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 347287) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 347287) = 1/(347287 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15690 : Bounds (-132200469 / 125000000) (-846083 / 800000) (Real.log (347287 / 1000000)) := by
  have h := reflection_log_15690_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15691_neg : (503006131 / 1000000000) ≤ -Real.log (200000 / 330737) ∧
    -Real.log (200000 / 330737) ≤ (125751533 / 250000000) := by
  have h := checkLog_sound (w := (130737 / 530737)) (n := 12)
    (lo := (503006131 / 1000000000)) (hi := (125751533 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330737 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330737 / 200000) = 1/(200000 / 330737) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15691 : Bounds (503006131 / 1000000000) (125751533 / 250000000) (Real.log (330737 / 200000)) := by
  have h := reflection_log_15691_neg
  have he : Real.log (330737 / 200000) = -Real.log (200000 / 330737) := by
    rw [show ((330737 / 200000) : ℝ) = ((200000 / 330737) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15692_neg : (66275407 / 62500000) ≤ -Real.log (69263 / 200000) ∧
    -Real.log (69263 / 200000) ≤ (530203257 / 500000000) := by
  have h := checkLog_sound (w := (30737 / 169263)) (n := 12)
    (lo := (91814833 / 250000000)) (hi := (367259333 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69263) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69263) = 1/(69263 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15692 : Bounds (-530203257 / 500000000) (-66275407 / 62500000) (Real.log (69263 / 200000)) := by
  have h := reflection_log_15692_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15693_neg : (278700191 / 500000000) ≤ -Real.log (22907836831 / 40000000000) ∧
    -Real.log (22907836831 / 40000000000) ≤ (557400383 / 1000000000) := by
  have h := checkLog_sound (w := (17092163169 / 62907836831)) (n := 12)
    (lo := (278700191 / 500000000)) (hi := (557400383 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22907836831) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22907836831) = 1/(22907836831 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15693 : Bounds (-557400383 / 1000000000) (-278700191 / 500000000) (Real.log (22907836831 / 40000000000)) := by
  have h := reflection_log_15693_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15694_neg : (555185571 / 1000000000) ≤ -Real.log (573965739631 / 1000000000000) ∧
    -Real.log (573965739631 / 1000000000000) ≤ (138796393 / 250000000) := by
  have h := checkLog_sound (w := (426034260369 / 1573965739631)) (n := 12)
    (lo := (555185571 / 1000000000)) (hi := (138796393 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573965739631) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573965739631) = 1/(573965739631 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15694 : Bounds (-138796393 / 250000000) (-555185571 / 1000000000) (Real.log (573965739631 / 1000000000000)) := by
  have h := reflection_log_15694_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15695_neg : (156002193 / 100000000) ≤ -Real.log (250000000000 / 1189731403709) ∧
    -Real.log (250000000000 / 1189731403709) ≤ (1560021933 / 1000000000) := by
  have h := checkLog_sound (w := (189731403709 / 2189731403709)) (n := 12)
    (lo := (17372757 / 100000000)) (hi := (173727571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1189731403709 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1189731403709 / 1000000000000) = 1/(250000000000 / 1189731403709) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15695 : Bounds (156002193 / 100000000) (1560021933 / 1000000000) (Real.log (1189731403709 / 250000000000)) := by
  have h := reflection_log_15695_neg
  have he : Real.log (1189731403709 / 250000000000) = -Real.log (250000000000 / 1189731403709) := by
    rw [show ((1189731403709 / 250000000000) : ℝ) = ((250000000000 / 1189731403709) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15696_neg : (1563412643 / 1000000000) ≤ -Real.log (50000000000 / 238754457647) ∧
    -Real.log (50000000000 / 238754457647) ≤ (781706323 / 500000000) := by
  have h := checkLog_sound (w := (38754457647 / 438754457647)) (n := 12)
    (lo := (177118283 / 1000000000)) (hi := (44279571 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((238754457647 / 200000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(238754457647 / 200000000000) = 1/(50000000000 / 238754457647) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15696 : Bounds (1563412643 / 1000000000) (781706323 / 500000000) (Real.log (238754457647 / 50000000000)) := by
  have h := reflection_log_15696_neg
  have he : Real.log (238754457647 / 50000000000) = -Real.log (50000000000 / 238754457647) := by
    rw [show ((238754457647 / 50000000000) : ℝ) = ((50000000000 / 238754457647) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15697_neg : (6500789039 / 1000000000) ≤ -Real.log (500000000000 / 332833333333333) ∧
    -Real.log (500000000000 / 332833333333333) ≤ (6500789049 / 1000000000) := by
  have h := checkLog_sound (w := (76833333333333 / 588833333333333)) (n := 12)
    (lo := (262464419 / 1000000000)) (hi := (13123221 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((332833333333333 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(332833333333333 / 256000000000000) = 1/(500000000000 / 332833333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15697 : Bounds (6500789039 / 1000000000) (6500789049 / 1000000000) (Real.log (332833333333333 / 500000000000)) := by
  have h := reflection_log_15697_neg
  have he : Real.log (332833333333333 / 500000000000) = -Real.log (500000000000 / 332833333333333) := by
    rw [show ((332833333333333 / 500000000000) : ℝ) = ((500000000000 / 332833333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15698_neg : (821235257 / 125000000) ≤ -Real.log (250000000000 / 178321428571429) ∧
    -Real.log (250000000000 / 178321428571429) ≤ (3284941033 / 500000000) := by
  have h := checkLog_sound (w := (50321428571429 / 306321428571429)) (n := 12)
    (lo := (82889359 / 250000000)) (hi := (331557437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((178321428571429 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(178321428571429 / 128000000000000) = 1/(250000000000 / 178321428571429) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15698 : Bounds (821235257 / 125000000) (3284941033 / 500000000) (Real.log (178321428571429 / 250000000000)) := by
  have h := reflection_log_15698_neg
  have he : Real.log (178321428571429 / 250000000000) = -Real.log (250000000000 / 178321428571429) := by
    rw [show ((178321428571429 / 250000000000) : ℝ) = ((250000000000 / 178321428571429) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15699_neg : (345923167 / 500000000) ≤ -Real.log (5000 / 9987) ∧
    -Real.log (5000 / 9987) ≤ (138369267 / 200000000) := by
  have h := checkLog_sound (w := (4987 / 14987)) (n := 12)
    (lo := (345923167 / 500000000)) (hi := (138369267 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9987 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9987 / 5000) = 1/(5000 / 9987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15699 : Bounds (345923167 / 500000000) (138369267 / 200000000) (Real.log (9987 / 5000)) := by
  have h := reflection_log_15699_neg
  have he : Real.log (9987 / 5000) = -Real.log (5000 / 9987) := by
    rw [show ((9987 / 5000) : ℝ) = ((5000 / 9987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15700_neg : (5952243829 / 1000000000) ≤ -Real.log (13 / 5000) ∧
    -Real.log (13 / 5000) ≤ (2976121919 / 500000000) := by
  have h := checkLog_sound (w := (209 / 1041)) (n := 12)
    (lo := (407066389 / 1000000000)) (hi := (40706639 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 416) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 416) = 1/(13 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15700 : Bounds (-2976121919 / 500000000) (-5952243829 / 1000000000) (Real.log (13 / 5000)) := by
  have h := reflection_log_15700_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15701_neg : (498451 / 500000000) ≤ -Real.log (5000000 / 5004987) ∧
    -Real.log (5000000 / 5004987) ≤ (996903 / 1000000000) := by
  have h := checkLog_sound (w := (4987 / 10004987)) (n := 12)
    (lo := (498451 / 500000000)) (hi := (996903 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004987 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004987 / 5000000) = 1/(5000000 / 5004987) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15701 : Bounds (498451 / 500000000) (996903 / 1000000000) (Real.log (5004987 / 5000000)) := by
  have h := reflection_log_15701_neg
  have he : Real.log (5004987 / 5000000) = -Real.log (5000000 / 5004987) := by
    rw [show ((5004987 / 5000000) : ℝ) = ((5000000 / 5004987) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15702_neg : (997897 / 1000000000) ≤ -Real.log (4995013 / 5000000) ∧
    -Real.log (4995013 / 5000000) ≤ (498949 / 500000000) := by
  have h := checkLog_sound (w := (4987 / 9995013)) (n := 12)
    (lo := (997897 / 1000000000)) (hi := (498949 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995013) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995013) = 1/(4995013 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15702 : Bounds (-498949 / 500000000) (-997897 / 1000000000) (Real.log (4995013 / 5000000)) := by
  have h := reflection_log_15702_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15703_neg : (50262993 / 100000000) ≤ -Real.log (1000000 / 1653063) ∧
    -Real.log (1000000 / 1653063) ≤ (502629931 / 1000000000) := by
  have h := checkLog_sound (w := (653063 / 2653063)) (n := 12)
    (lo := (50262993 / 100000000)) (hi := (502629931 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653063 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653063 / 1000000) = 1/(1000000 / 1653063) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15703 : Bounds (50262993 / 100000000) (502629931 / 1000000000) (Real.log (1653063 / 1000000)) := by
  have h := reflection_log_15703_neg
  have he : Real.log (1653063 / 1000000) = -Real.log (1000000 / 1653063) := by
    rw [show ((1653063 / 1000000) : ℝ) = ((1000000 / 1653063) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15704_neg : (1058612071 / 1000000000) ≤ -Real.log (346937 / 1000000) ∧
    -Real.log (346937 / 1000000) ≤ (1058612073 / 1000000000) := by
  have h := checkLog_sound (w := (153063 / 846937)) (n := 12)
    (lo := (365464891 / 1000000000)) (hi := (91366223 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346937) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346937) = 1/(346937 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15704 : Bounds (-1058612073 / 1000000000) (-1058612071 / 1000000000) (Real.log (346937 / 1000000)) := by
  have h := reflection_log_15704_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15705_neg : (50321957 / 100000000) ≤ -Real.log (500000 / 827019) ∧
    -Real.log (500000 / 827019) ≤ (503219571 / 1000000000) := by
  have h := checkLog_sound (w := (327019 / 1327019)) (n := 12)
    (lo := (50321957 / 100000000)) (hi := (503219571 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((827019 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(827019 / 500000) = 1/(500000 / 827019) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15705 : Bounds (50321957 / 100000000) (503219571 / 1000000000) (Real.log (827019 / 500000)) := by
  have h := reflection_log_15705_neg
  have he : Real.log (827019 / 500000) = -Real.log (500000 / 827019) := by
    rw [show ((827019 / 500000) : ℝ) = ((500000 / 827019) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15706_neg : (212285267 / 200000000) ≤ -Real.log (172981 / 500000) ∧
    -Real.log (172981 / 500000) ≤ (1061426337 / 1000000000) := by
  have h := checkLog_sound (w := (77019 / 422981)) (n := 12)
    (lo := (73655831 / 200000000)) (hi := (92069789 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 172981) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 172981) = 1/(172981 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15706 : Bounds (-1061426337 / 1000000000) (-212285267 / 200000000) (Real.log (172981 / 500000)) := by
  have h := reflection_log_15706_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15707_neg : (111641353 / 200000000) ≤ -Real.log (143058573639 / 250000000000) ∧
    -Real.log (143058573639 / 250000000000) ≤ (279103383 / 500000000) := by
  have h := checkLog_sound (w := (106941426361 / 393058573639)) (n := 12)
    (lo := (111641353 / 200000000)) (hi := (279103383 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143058573639) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143058573639) = 1/(143058573639 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15707 : Bounds (-279103383 / 500000000) (-111641353 / 200000000) (Real.log (143058573639 / 250000000000)) := by
  have h := reflection_log_15707_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15708_neg : (555982141 / 1000000000) ≤ -Real.log (573508718031 / 1000000000000) ∧
    -Real.log (573508718031 / 1000000000000) ≤ (277991071 / 500000000) := by
  have h := checkLog_sound (w := (426491281969 / 1573508718031)) (n := 12)
    (lo := (555982141 / 1000000000)) (hi := (277991071 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573508718031) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573508718031) = 1/(573508718031 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15708 : Bounds (-277991071 / 500000000) (-555982141 / 1000000000) (Real.log (573508718031 / 1000000000000)) := by
  have h := reflection_log_15708_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15709_neg : (1561242001 / 1000000000) ≤ -Real.log (500000000000 / 2382367692117) ∧
    -Real.log (500000000000 / 2382367692117) ≤ (390310501 / 250000000) := by
  have h := checkLog_sound (w := (382367692117 / 4382367692117)) (n := 12)
    (lo := (174947641 / 1000000000)) (hi := (87473821 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2382367692117 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2382367692117 / 2000000000000) = 1/(500000000000 / 2382367692117) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15709 : Bounds (1561242001 / 1000000000) (390310501 / 250000000) (Real.log (2382367692117 / 500000000000)) := by
  have h := reflection_log_15709_neg
  have he : Real.log (2382367692117 / 500000000000) = -Real.log (500000000000 / 2382367692117) := by
    rw [show ((2382367692117 / 500000000000) : ℝ) = ((500000000000 / 2382367692117) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15710_neg : (782322953 / 500000000) ≤ -Real.log (500000000000 / 2390490863159) ∧
    -Real.log (500000000000 / 2390490863159) ≤ (1564645909 / 1000000000) := by
  have h := checkLog_sound (w := (390490863159 / 4390490863159)) (n := 12)
    (lo := (89175773 / 500000000)) (hi := (178351547 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2390490863159 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2390490863159 / 2000000000000) = 1/(500000000000 / 2390490863159) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15710 : Bounds (782322953 / 500000000) (1564645909 / 1000000000) (Real.log (2390490863159 / 500000000000)) := by
  have h := reflection_log_15710_neg
  have he : Real.log (2390490863159 / 500000000000) = -Real.log (500000000000 / 2390490863159) := by
    rw [show ((2390490863159 / 500000000000) : ℝ) = ((500000000000 / 2390490863159) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15711_neg : (821235257 / 125000000) ≤ -Real.log (500000000000 / 356642857142857) ∧
    -Real.log (500000000000 / 356642857142857) ≤ (3284941033 / 500000000) := by
  have h := checkLog_sound (w := (100642857142857 / 612642857142857)) (n := 12)
    (lo := (82889359 / 250000000)) (hi := (331557437 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356642857142857 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(356642857142857 / 256000000000000) = 1/(500000000000 / 356642857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15711 : Bounds (821235257 / 125000000) (3284941033 / 500000000) (Real.log (356642857142857 / 500000000000)) := by
  have h := reflection_log_15711_neg
  have he : Real.log (356642857142857 / 500000000000) = -Real.log (500000000000 / 356642857142857) := by
    rw [show ((356642857142857 / 500000000000) : ℝ) = ((500000000000 / 356642857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15712_neg : (6644090163 / 1000000000) ≤ -Real.log (100000000000 / 76823076923077) ∧
    -Real.log (100000000000 / 76823076923077) ≤ (6644090173 / 1000000000) := by
  have h := checkLog_sound (w := (25623076923077 / 128023076923077)) (n := 12)
    (lo := (405765543 / 1000000000)) (hi := (50720693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((76823076923077 / 51200000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(76823076923077 / 51200000000000) = 1/(100000000000 / 76823076923077) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15712 : Bounds (6644090163 / 1000000000) (6644090173 / 1000000000) (Real.log (76823076923077 / 100000000000)) := by
  have h := reflection_log_15712_neg
  have he : Real.log (76823076923077 / 100000000000) = -Real.log (100000000000 / 76823076923077) := by
    rw [show ((76823076923077 / 100000000000) : ℝ) = ((100000000000 / 76823076923077) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15713_neg : (691946459 / 1000000000) ≤ -Real.log (1250 / 2497) ∧
    -Real.log (1250 / 2497) ≤ (34597323 / 50000000) := by
  have h := checkLog_sound (w := (1247 / 3747)) (n := 12)
    (lo := (691946459 / 1000000000)) (hi := (34597323 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2497 / 1250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2497 / 1250) = 1/(1250 / 2497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15713 : Bounds (691946459 / 1000000000) (34597323 / 50000000) (Real.log (2497 / 1250)) := by
  have h := reflection_log_15713_neg
  have he : Real.log (2497 / 1250) = -Real.log (1250 / 2497) := by
    rw [show ((2497 / 1250) : ℝ) = ((1250 / 2497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15714_neg : (6032286537 / 1000000000) ≤ -Real.log (3 / 1250) ∧
    -Real.log (3 / 1250) ≤ (3016143273 / 500000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 384) = 1/(3 / 1250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15714 : Bounds (-3016143273 / 500000000) (-6032286537 / 1000000000) (Real.log (3 / 1250)) := by
  have h := reflection_log_15714_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15715_neg : (498551 / 500000000) ≤ -Real.log (1250000 / 1251247) ∧
    -Real.log (1250000 / 1251247) ≤ (997103 / 1000000000) := by
  have h := checkLog_sound (w := (1247 / 2501247)) (n := 12)
    (lo := (498551 / 500000000)) (hi := (997103 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1251247 / 1250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1251247 / 1250000) = 1/(1250000 / 1251247) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15715 : Bounds (498551 / 500000000) (997103 / 1000000000) (Real.log (1251247 / 1250000)) := by
  have h := reflection_log_15715_neg
  have he : Real.log (1251247 / 1250000) = -Real.log (1250000 / 1251247) := by
    rw [show ((1251247 / 1250000) : ℝ) = ((1250000 / 1251247) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15716_neg : (998097 / 1000000000) ≤ -Real.log (1248753 / 1250000) ∧
    -Real.log (1248753 / 1250000) ≤ (499049 / 500000000) := by
  have h := checkLog_sound (w := (1247 / 2498753)) (n := 12)
    (lo := (998097 / 1000000000)) (hi := (499049 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1250000 / 1248753) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1250000 / 1248753) = 1/(1248753 / 1250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15716 : Bounds (-499049 / 500000000) (-998097 / 1000000000) (Real.log (1248753 / 1250000)) := by
  have h := reflection_log_15716_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15717_neg : (100568811 / 200000000) ≤ -Real.log (1000000 / 1653417) ∧
    -Real.log (1000000 / 1653417) ≤ (62855507 / 125000000) := by
  have h := checkLog_sound (w := (653417 / 2653417)) (n := 12)
    (lo := (100568811 / 200000000)) (hi := (62855507 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1653417 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1653417 / 1000000) = 1/(1000000 / 1653417) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15717 : Bounds (100568811 / 200000000) (62855507 / 125000000) (Real.log (1653417 / 1000000)) := by
  have h := reflection_log_15717_neg
  have he : Real.log (1653417 / 1000000) = -Real.log (1000000 / 1653417) := by
    rw [show ((1653417 / 1000000) : ℝ) = ((1000000 / 1653417) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15718_neg : (21192659 / 20000000) ≤ -Real.log (346583 / 1000000) ∧
    -Real.log (346583 / 1000000) ≤ (132454119 / 125000000) := by
  have h := checkLog_sound (w := (153417 / 846583)) (n := 12)
    (lo := (36648577 / 100000000)) (hi := (366485771 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 346583) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 346583) = 1/(346583 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15718 : Bounds (-132454119 / 125000000) (-21192659 / 20000000) (Real.log (346583 / 1000000)) := by
  have h := reflection_log_15718_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15719_neg : (503435383 / 1000000000) ≤ -Real.log (200000 / 330879) ∧
    -Real.log (200000 / 330879) ≤ (62929423 / 125000000) := by
  have h := checkLog_sound (w := (130879 / 530879)) (n := 12)
    (lo := (503435383 / 1000000000)) (hi := (62929423 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330879 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330879 / 200000) = 1/(200000 / 330879) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15719 : Bounds (503435383 / 1000000000) (62929423 / 125000000) (Real.log (330879 / 200000)) := by
  have h := reflection_log_15719_neg
  have he : Real.log (330879 / 200000) = -Real.log (200000 / 330879) := by
    rw [show ((330879 / 200000) : ℝ) = ((200000 / 330879) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15720_neg : (531229387 / 500000000) ≤ -Real.log (69121 / 200000) ∧
    -Real.log (69121 / 200000) ≤ (132807347 / 125000000) := by
  have h := checkLog_sound (w := (30879 / 169121)) (n := 12)
    (lo := (184655797 / 500000000)) (hi := (73862319 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69121) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69121) = 1/(69121 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15720 : Bounds (-132807347 / 125000000) (-531229387 / 500000000) (Real.log (69121 / 200000)) := by
  have h := reflection_log_15720_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15721_neg : (559023391 / 1000000000) ≤ -Real.log (22870687359 / 40000000000) ∧
    -Real.log (22870687359 / 40000000000) ≤ (17469481 / 31250000) := by
  have h := checkLog_sound (w := (17129312641 / 62870687359)) (n := 12)
    (lo := (559023391 / 1000000000)) (hi := (17469481 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22870687359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22870687359) = 1/(22870687359 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15721 : Bounds (-17469481 / 31250000) (-559023391 / 1000000000) (Real.log (22870687359 / 40000000000)) := by
  have h := reflection_log_15721_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15722_neg : (111357779 / 200000000) ≤ -Real.log (573046224111 / 1000000000000) ∧
    -Real.log (573046224111 / 1000000000000) ≤ (17399653 / 31250000) := by
  have h := checkLog_sound (w := (426953775889 / 1573046224111)) (n := 12)
    (lo := (111357779 / 200000000)) (hi := (17399653 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 573046224111) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 573046224111) = 1/(573046224111 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15722 : Bounds (-17399653 / 31250000) (-111357779 / 200000000) (Real.log (573046224111 / 1000000000000)) := by
  have h := reflection_log_15722_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15723_neg : (312495401 / 200000000) ≤ -Real.log (500000000000 / 2385311743507) ∧
    -Real.log (500000000000 / 2385311743507) ≤ (97654813 / 62500000) := by
  have h := checkLog_sound (w := (385311743507 / 4385311743507)) (n := 12)
    (lo := (35236529 / 200000000)) (hi := (88091323 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2385311743507 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2385311743507 / 2000000000000) = 1/(500000000000 / 2385311743507) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15723 : Bounds (312495401 / 200000000) (97654813 / 62500000) (Real.log (2385311743507 / 500000000000)) := by
  have h := reflection_log_15723_neg
  have he : Real.log (2385311743507 / 500000000000) = -Real.log (500000000000 / 2385311743507) := by
    rw [show ((2385311743507 / 500000000000) : ℝ) = ((500000000000 / 2385311743507) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15724_neg : (391473539 / 250000000) ≤ -Real.log (250000000000 / 1196738328439) ∧
    -Real.log (250000000000 / 1196738328439) ≤ (1565894159 / 1000000000) := by
  have h := checkLog_sound (w := (196738328439 / 2196738328439)) (n := 12)
    (lo := (44899949 / 250000000)) (hi := (179599797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1196738328439 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1196738328439 / 1000000000000) = 1/(250000000000 / 1196738328439) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15724 : Bounds (391473539 / 250000000) (1565894159 / 1000000000) (Real.log (1196738328439 / 250000000000)) := by
  have h := reflection_log_15724_neg
  have he : Real.log (1196738328439 / 250000000000) = -Real.log (250000000000 / 1196738328439) := by
    rw [show ((1196738328439 / 250000000000) : ℝ) = ((250000000000 / 1196738328439) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15725_neg : (6644090163 / 1000000000) ≤ -Real.log (62500000000 / 48014423076923) ∧
    -Real.log (62500000000 / 48014423076923) ≤ (6644090173 / 1000000000) := by
  have h := checkLog_sound (w := (16014423076923 / 80014423076923)) (n := 12)
    (lo := (405765543 / 1000000000)) (hi := (50720693 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((48014423076923 / 32000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(48014423076923 / 32000000000000) = 1/(62500000000 / 48014423076923) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15725 : Bounds (6644090163 / 1000000000) (6644090173 / 1000000000) (Real.log (48014423076923 / 62500000000)) := by
  have h := reflection_log_15725_neg
  have he : Real.log (48014423076923 / 62500000000) = -Real.log (62500000000 / 48014423076923) := by
    rw [show ((48014423076923 / 62500000000) : ℝ) = ((62500000000 / 48014423076923) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15726_neg : (1681058249 / 250000000) ≤ -Real.log (500000000000 / 416166666666667) ∧
    -Real.log (500000000000 / 416166666666667) ≤ (3362116503 / 500000000) := by
  have h := checkLog_sound (w := (160166666666667 / 672166666666667)) (n := 12)
    (lo := (60738547 / 125000000)) (hi := (485908377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((416166666666667 / 256000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(416166666666667 / 256000000000000) = 1/(500000000000 / 416166666666667) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15726 : Bounds (1681058249 / 250000000) (3362116503 / 500000000) (Real.log (416166666666667 / 500000000000)) := by
  have h := reflection_log_15726_neg
  have he : Real.log (416166666666667 / 500000000000) = -Real.log (500000000000 / 416166666666667) := by
    rw [show ((416166666666667 / 500000000000) : ℝ) = ((500000000000 / 416166666666667) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15727_neg : (27681863 / 40000000) ≤ -Real.log (5000 / 9989) ∧
    -Real.log (5000 / 9989) ≤ (43252911 / 62500000) := by
  have h := checkLog_sound (w := (4989 / 14989)) (n := 12)
    (lo := (27681863 / 40000000)) (hi := (43252911 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9989 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9989 / 5000) = 1/(5000 / 9989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15727 : Bounds (27681863 / 40000000) (43252911 / 62500000) (Real.log (9989 / 5000)) := by
  have h := reflection_log_15727_neg
  have he : Real.log (9989 / 5000) = -Real.log (5000 / 9989) := by
    rw [show ((9989 / 5000) : ℝ) = ((5000 / 9989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15728_neg : (3059648957 / 500000000) ≤ -Real.log (11 / 5000) ∧
    -Real.log (11 / 5000) ≤ (6119297923 / 1000000000) := by
  have h := checkLog_sound (w := (273 / 977)) (n := 12)
    (lo := (287060237 / 500000000)) (hi := (22964819 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 352) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(625 / 352) = 1/(11 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15728 : Bounds (-6119297923 / 1000000000) (-3059648957 / 500000000) (Real.log (11 / 5000)) := by
  have h := reflection_log_15728_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15729_neg : (498651 / 500000000) ≤ -Real.log (5000000 / 5004989) ∧
    -Real.log (5000000 / 5004989) ≤ (997303 / 1000000000) := by
  have h := checkLog_sound (w := (4989 / 10004989)) (n := 12)
    (lo := (498651 / 500000000)) (hi := (997303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004989 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004989 / 5000000) = 1/(5000000 / 5004989) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15729 : Bounds (498651 / 500000000) (997303 / 1000000000) (Real.log (5004989 / 5000000)) := by
  have h := reflection_log_15729_neg
  have he : Real.log (5004989 / 5000000) = -Real.log (5000000 / 5004989) := by
    rw [show ((5004989 / 5000000) : ℝ) = ((5000000 / 5004989) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15730_neg : (499149 / 500000000) ≤ -Real.log (4995011 / 5000000) ∧
    -Real.log (4995011 / 5000000) ≤ (998299 / 1000000000) := by
  have h := checkLog_sound (w := (4989 / 9995011)) (n := 12)
    (lo := (499149 / 500000000)) (hi := (998299 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995011) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995011) = 1/(4995011 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15730 : Bounds (-998299 / 1000000000) (-499149 / 500000000) (Real.log (4995011 / 5000000)) := by
  have h := reflection_log_15730_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15731_neg : (125764987 / 250000000) ≤ -Real.log (500000 / 826887) ∧
    -Real.log (500000 / 826887) ≤ (503059949 / 1000000000) := by
  have h := checkLog_sound (w := (326887 / 1326887)) (n := 12)
    (lo := (125764987 / 250000000)) (hi := (503059949 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((826887 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(826887 / 500000) = 1/(500000 / 826887) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15731 : Bounds (125764987 / 250000000) (503059949 / 1000000000) (Real.log (826887 / 500000)) := by
  have h := reflection_log_15731_neg
  have he : Real.log (826887 / 500000) = -Real.log (500000 / 826887) := by
    rw [show ((826887 / 500000) : ℝ) = ((500000 / 826887) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15732_neg : (1060663537 / 1000000000) ≤ -Real.log (173113 / 500000) ∧
    -Real.log (173113 / 500000) ≤ (1060663539 / 1000000000) := by
  have h := checkLog_sound (w := (76887 / 423113)) (n := 12)
    (lo := (367516357 / 1000000000)) (hi := (183758179 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000 / 173113) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(250000 / 173113) = 1/(173113 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15732 : Bounds (-1060663539 / 1000000000) (-1060663537 / 1000000000) (Real.log (173113 / 500000)) := by
  have h := reflection_log_15732_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15733_neg : (503652961 / 1000000000) ≤ -Real.log (200000 / 330951) ∧
    -Real.log (200000 / 330951) ≤ (251826481 / 500000000) := by
  have h := checkLog_sound (w := (130951 / 530951)) (n := 12)
    (lo := (503652961 / 1000000000)) (hi := (251826481 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330951 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330951 / 200000) = 1/(200000 / 330951) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15733 : Bounds (503652961 / 1000000000) (251826481 / 500000000) (Real.log (330951 / 200000)) := by
  have h := reflection_log_15733_neg
  have he : Real.log (330951 / 200000) = -Real.log (200000 / 330951) := by
    rw [show ((330951 / 200000) : ℝ) = ((200000 / 330951) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15734_neg : (132937621 / 125000000) ≤ -Real.log (69049 / 200000) ∧
    -Real.log (69049 / 200000) ≤ (106350097 / 100000000) := by
  have h := checkLog_sound (w := (30951 / 169049)) (n := 12)
    (lo := (92588447 / 250000000)) (hi := (370353789 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69049) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69049) = 1/(69049 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15734 : Bounds (-106350097 / 100000000) (-132937621 / 125000000) (Real.log (69049 / 200000)) := by
  have h := reflection_log_15734_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15735_neg : (559848007 / 1000000000) ≤ -Real.log (22851835599 / 40000000000) ∧
    -Real.log (22851835599 / 40000000000) ≤ (69981001 / 125000000) := by
  have h := checkLog_sound (w := (17148164401 / 62851835599)) (n := 12)
    (lo := (559848007 / 1000000000)) (hi := (69981001 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22851835599) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22851835599) = 1/(22851835599 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15735 : Bounds (-69981001 / 125000000) (-559848007 / 1000000000) (Real.log (22851835599 / 40000000000)) := by
  have h := reflection_log_15735_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15736_neg : (557603589 / 1000000000) ≤ -Real.log (143144889231 / 250000000000) ∧
    -Real.log (143144889231 / 250000000000) ≤ (55760359 / 100000000) := by
  have h := checkLog_sound (w := (106855110769 / 393144889231)) (n := 12)
    (lo := (557603589 / 1000000000)) (hi := (55760359 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 143144889231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 143144889231) = 1/(143144889231 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15736 : Bounds (-55760359 / 100000000) (-557603589 / 1000000000) (Real.log (143144889231 / 250000000000)) := by
  have h := reflection_log_15736_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15737_neg : (312744697 / 200000000) ≤ -Real.log (250000000000 / 1194143420771) ∧
    -Real.log (250000000000 / 1194143420771) ≤ (48866359 / 31250000) := by
  have h := checkLog_sound (w := (194143420771 / 2194143420771)) (n := 12)
    (lo := (1419433 / 8000000)) (hi := (88714563 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1194143420771 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1194143420771 / 1000000000000) = 1/(250000000000 / 1194143420771) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15737 : Bounds (312744697 / 200000000) (48866359 / 31250000) (Real.log (1194143420771 / 250000000000)) := by
  have h := reflection_log_15737_neg
  have he : Real.log (1194143420771 / 250000000000) = -Real.log (250000000000 / 1194143420771) := by
    rw [show ((1194143420771 / 250000000000) : ℝ) = ((250000000000 / 1194143420771) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15738_neg : (1567153929 / 1000000000) ≤ -Real.log (500000000000 / 2396493794263) ∧
    -Real.log (500000000000 / 2396493794263) ≤ (391788483 / 250000000) := by
  have h := checkLog_sound (w := (396493794263 / 4396493794263)) (n := 12)
    (lo := (180859569 / 1000000000)) (hi := (18085957 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2396493794263 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2396493794263 / 2000000000000) = 1/(500000000000 / 2396493794263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15738 : Bounds (1567153929 / 1000000000) (391788483 / 250000000) (Real.log (2396493794263 / 500000000000)) := by
  have h := reflection_log_15738_neg
  have he : Real.log (2396493794263 / 500000000000) = -Real.log (500000000000 / 2396493794263) := by
    rw [show ((2396493794263 / 500000000000) : ℝ) = ((500000000000 / 2396493794263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15739_neg : (1681058249 / 250000000) ≤ -Real.log (250000000000 / 208083333333333) ∧
    -Real.log (250000000000 / 208083333333333) ≤ (3362116503 / 500000000) := by
  have h := checkLog_sound (w := (80083333333333 / 336083333333333)) (n := 12)
    (lo := (60738547 / 125000000)) (hi := (485908377 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((208083333333333 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(208083333333333 / 128000000000000) = 1/(250000000000 / 208083333333333) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15739 : Bounds (1681058249 / 250000000) (3362116503 / 500000000) (Real.log (208083333333333 / 250000000000)) := by
  have h := reflection_log_15739_neg
  have he : Real.log (208083333333333 / 250000000000) = -Real.log (250000000000 / 208083333333333) := by
    rw [show ((208083333333333 / 250000000000) : ℝ) = ((250000000000 / 208083333333333) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15740_neg : (851418061 / 125000000) ≤ -Real.log (100000000000 / 90809090909091) ∧
    -Real.log (100000000000 / 90809090909091) ≤ (3405672249 / 500000000) := by
  have h := checkLog_sound (w := (39609090909091 / 142009090909091)) (n := 12)
    (lo := (143254967 / 250000000)) (hi := (573019869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((90809090909091 / 51200000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(90809090909091 / 51200000000000) = 1/(100000000000 / 90809090909091) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15740 : Bounds (851418061 / 125000000) (3405672249 / 500000000) (Real.log (90809090909091 / 100000000000)) := by
  have h := reflection_log_15740_neg
  have he : Real.log (90809090909091 / 100000000000) = -Real.log (100000000000 / 90809090909091) := by
    rw [show ((90809090909091 / 100000000000) : ℝ) = ((100000000000 / 90809090909091) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15741_neg : (17303667 / 25000000) ≤ -Real.log (500 / 999) ∧
    -Real.log (500 / 999) ≤ (692146681 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 1499)) (n := 12)
    (lo := (17303667 / 25000000)) (hi := (692146681 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(999 / 500) = 1/(500 / 999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15741 : Bounds (17303667 / 25000000) (692146681 / 1000000000) (Real.log (999 / 500)) := by
  have h := reflection_log_15741_neg
  have he : Real.log (999 / 500) = -Real.log (500 / 999) := by
    rw [show ((999 / 500) : ℝ) = ((500 / 999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15742_neg : (6214608093 / 1000000000) ≤ -Real.log (1 / 500) ∧
    -Real.log (1 / 500) ≤ (3107304051 / 500000000) := by
  have h := checkLog_sound (w := (61 / 189)) (n := 12)
    (lo := (669430653 / 1000000000)) (hi := (334715327 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125 / 64) : ℝ) 8 (by norm_num)
  have hq : (2 : ℝ)^8*(125 / 64) = 1/(1 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15742 : Bounds (-3107304051 / 500000000) (-6214608093 / 1000000000) (Real.log (1 / 500)) := by
  have h := reflection_log_15742_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15743_neg : (498751 / 500000000) ≤ -Real.log (500000 / 500499) ∧
    -Real.log (500000 / 500499) ≤ (997503 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 1000499)) (n := 12)
    (lo := (498751 / 500000000)) (hi := (997503 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500499 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500499 / 500000) = 1/(500000 / 500499) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15743 : Bounds (498751 / 500000000) (997503 / 1000000000) (Real.log (500499 / 500000)) := by
  have h := reflection_log_15743_neg
  have he : Real.log (500499 / 500000) = -Real.log (500000 / 500499) := by
    rw [show ((500499 / 500000) : ℝ) = ((500000 / 500499) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0246 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_15744_neg : (499249 / 500000000) ≤ -Real.log (499501 / 500000) ∧
    -Real.log (499501 / 500000) ≤ (998499 / 1000000000) := by
  have h := checkLog_sound (w := (499 / 999501)) (n := 12)
    (lo := (499249 / 500000000)) (hi := (998499 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499501) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499501) = 1/(499501 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15744 : Bounds (-998499 / 1000000000) (-499249 / 500000000) (Real.log (499501 / 500000)) := by
  have h := reflection_log_15744_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15745_neg : (503278213 / 1000000000) ≤ -Real.log (200000 / 330827) ∧
    -Real.log (200000 / 330827) ≤ (251639107 / 500000000) := by
  have h := checkLog_sound (w := (130827 / 530827)) (n := 12)
    (lo := (503278213 / 1000000000)) (hi := (251639107 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((330827 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(330827 / 200000) = 1/(200000 / 330827) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15745 : Bounds (503278213 / 1000000000) (251639107 / 500000000) (Real.log (330827 / 200000)) := by
  have h := reflection_log_15745_neg
  have he : Real.log (330827 / 200000) = -Real.log (200000 / 330827) := by
    rw [show ((330827 / 200000) : ℝ) = ((200000 / 330827) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15746_neg : (2073646 / 1953125) ≤ -Real.log (69173 / 200000) ∧
    -Real.log (69173 / 200000) ≤ (530853377 / 500000000) := by
  have h := checkLog_sound (w := (30827 / 169173)) (n := 12)
    (lo := (92139893 / 250000000)) (hi := (368559573 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((100000 / 69173) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(100000 / 69173) = 1/(69173 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15746 : Bounds (-530853377 / 500000000) (-2073646 / 1953125) (Real.log (69173 / 200000)) := by
  have h := reflection_log_15746_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15747_neg : (503873513 / 1000000000) ≤ -Real.log (12500 / 20689) ∧
    -Real.log (12500 / 20689) ≤ (251936757 / 500000000) := by
  have h := checkLog_sound (w := (8189 / 33189)) (n := 12)
    (lo := (503873513 / 1000000000)) (hi := (251936757 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((20689 / 12500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(20689 / 12500) = 1/(12500 / 20689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15747 : Bounds (503873513 / 1000000000) (251936757 / 500000000) (Real.log (20689 / 12500)) := by
  have h := reflection_log_15747_neg
  have he : Real.log (20689 / 12500) = -Real.log (12500 / 20689) := by
    rw [show ((20689 / 12500) : ℝ) = ((12500 / 20689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15748_neg : (1064558747 / 1000000000) ≤ -Real.log (4311 / 12500) ∧
    -Real.log (4311 / 12500) ≤ (1064558749 / 1000000000) := by
  have h := checkLog_sound (w := (1939 / 10561)) (n := 12)
    (lo := (371411567 / 1000000000)) (hi := (23213223 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((6250 / 4311) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(6250 / 4311) = 1/(4311 / 12500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15748 : Bounds (-1064558749 / 1000000000) (-1064558747 / 1000000000) (Real.log (4311 / 12500)) := by
  have h := reflection_log_15748_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15749_neg : (280342617 / 500000000) ≤ -Real.log (89190279 / 156250000) ∧
    -Real.log (89190279 / 156250000) ≤ (112137047 / 200000000) := by
  have h := checkLog_sound (w := (67059721 / 245440279)) (n := 12)
    (lo := (280342617 / 500000000)) (hi := (112137047 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((156250000 / 89190279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(156250000 / 89190279) = 1/(89190279 / 156250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15749 : Bounds (-112137047 / 200000000) (-280342617 / 500000000) (Real.log (89190279 / 156250000)) := by
  have h := reflection_log_15749_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15750_neg : (558428539 / 1000000000) ≤ -Real.log (22884296071 / 40000000000) ∧
    -Real.log (22884296071 / 40000000000) ≤ (27921427 / 50000000) := by
  have h := checkLog_sound (w := (17115703929 / 62884296071)) (n := 12)
    (lo := (558428539 / 1000000000)) (hi := (27921427 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 22884296071) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 22884296071) = 1/(22884296071 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15750 : Bounds (-27921427 / 50000000) (-558428539 / 1000000000) (Real.log (22884296071 / 40000000000)) := by
  have h := reflection_log_15750_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15751_neg : (312996993 / 200000000) ≤ -Real.log (250000000000 / 1195650759689) ∧
    -Real.log (250000000000 / 1195650759689) ≤ (195623121 / 125000000) := by
  have h := checkLog_sound (w := (195650759689 / 2195650759689)) (n := 12)
    (lo := (35738121 / 200000000)) (hi := (89345303 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1195650759689 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1195650759689 / 1000000000000) = 1/(250000000000 / 1195650759689) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15751 : Bounds (312996993 / 200000000) (195623121 / 125000000) (Real.log (1195650759689 / 250000000000)) := by
  have h := reflection_log_15751_neg
  have he : Real.log (1195650759689 / 250000000000) = -Real.log (250000000000 / 1195650759689) := by
    rw [show ((1195650759689 / 250000000000) : ℝ) = ((250000000000 / 1195650759689) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15752_neg : (1568432261 / 1000000000) ≤ -Real.log (31250000000 / 149972454187) ∧
    -Real.log (31250000000 / 149972454187) ≤ (196054033 / 125000000) := by
  have h := checkLog_sound (w := (24972454187 / 274972454187)) (n := 12)
    (lo := (182137901 / 1000000000)) (hi := (91068951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((149972454187 / 125000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(149972454187 / 125000000000) = 1/(31250000000 / 149972454187) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15752 : Bounds (1568432261 / 1000000000) (196054033 / 125000000) (Real.log (149972454187 / 31250000000)) := by
  have h := reflection_log_15752_neg
  have he : Real.log (149972454187 / 31250000000) = -Real.log (31250000000 / 149972454187) := by
    rw [show ((149972454187 / 31250000000) : ℝ) = ((31250000000 / 149972454187) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15753_neg : (851418061 / 125000000) ≤ -Real.log (250000000000 / 227022727272727) ∧
    -Real.log (250000000000 / 227022727272727) ≤ (3405672249 / 500000000) := by
  have h := checkLog_sound (w := (99022727272727 / 355022727272727)) (n := 12)
    (lo := (143254967 / 250000000)) (hi := (573019869 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((227022727272727 / 128000000000000) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(227022727272727 / 128000000000000) = 1/(250000000000 / 227022727272727) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15753 : Bounds (851418061 / 125000000) (3405672249 / 500000000) (Real.log (227022727272727 / 250000000000)) := by
  have h := reflection_log_15753_neg
  have he : Real.log (227022727272727 / 250000000000) = -Real.log (250000000000 / 227022727272727) := by
    rw [show ((227022727272727 / 250000000000) : ℝ) = ((250000000000 / 227022727272727) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15754_neg : (6906754773 / 1000000000) ≤ -Real.log (1 / 999) ∧
    -Real.log (1 / 999) ≤ (6906754783 / 1000000000) := by
  have h := checkLog_sound (w := (487 / 1511)) (n := 12)
    (lo := (668430153 / 1000000000)) (hi := (334215077 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((999 / 512) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(999 / 512) = 1/(1 / 999) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15754 : Bounds (6906754773 / 1000000000) (6906754783 / 1000000000) (Real.log (999 / 1)) := by
  have h := reflection_log_15754_neg
  have he : Real.log (999 / 1) = -Real.log (1 / 999) := by
    rw [show ((999 / 1) : ℝ) = ((1 / 999) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15755_neg : (27689871 / 40000000) ≤ -Real.log (5000 / 9991) ∧
    -Real.log (5000 / 9991) ≤ (86530847 / 125000000) := by
  have h := checkLog_sound (w := (4991 / 14991)) (n := 12)
    (lo := (27689871 / 40000000)) (hi := (86530847 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9991 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9991 / 5000) = 1/(5000 / 9991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15755 : Bounds (27689871 / 40000000) (86530847 / 125000000) (Real.log (9991 / 5000)) := by
  have h := reflection_log_15755_neg
  have he : Real.log (9991 / 5000) = -Real.log (5000 / 9991) := by
    rw [show ((9991 / 5000) : ℝ) = ((5000 / 9991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15756_neg : (6319968609 / 1000000000) ≤ -Real.log (9 / 5000) ∧
    -Real.log (9 / 5000) ≤ (6319968619 / 1000000000) := by
  have h := checkLog_sound (w := (49 / 1201)) (n := 12)
    (lo := (81643989 / 1000000000)) (hi := (8164399 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 576) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 576) = 1/(9 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15756 : Bounds (-6319968619 / 1000000000) (-6319968609 / 1000000000) (Real.log (9 / 5000)) := by
  have h := reflection_log_15756_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15757_neg : (498851 / 500000000) ≤ -Real.log (5000000 / 5004991) ∧
    -Real.log (5000000 / 5004991) ≤ (997703 / 1000000000) := by
  have h := checkLog_sound (w := (4991 / 10004991)) (n := 12)
    (lo := (498851 / 500000000)) (hi := (997703 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004991 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004991 / 5000000) = 1/(5000000 / 5004991) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15757 : Bounds (498851 / 500000000) (997703 / 1000000000) (Real.log (5004991 / 5000000)) := by
  have h := reflection_log_15757_neg
  have he : Real.log (5004991 / 5000000) = -Real.log (5000000 / 5004991) := by
    rw [show ((5004991 / 5000000) : ℝ) = ((5000000 / 5004991) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15758_neg : (499349 / 500000000) ≤ -Real.log (4995009 / 5000000) ∧
    -Real.log (4995009 / 5000000) ≤ (998699 / 1000000000) := by
  have h := checkLog_sound (w := (4991 / 9995009)) (n := 12)
    (lo := (499349 / 500000000)) (hi := (998699 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995009) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995009) = 1/(4995009 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15758 : Bounds (-998699 / 1000000000) (-499349 / 500000000) (Real.log (4995009 / 5000000)) := by
  have h := reflection_log_15758_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15759_neg : (15734339 / 31250000) ≤ -Real.log (2000 / 3309) ∧
    -Real.log (2000 / 3309) ≤ (503498849 / 1000000000) := by
  have h := checkLog_sound (w := (1309 / 5309)) (n := 12)
    (lo := (15734339 / 31250000)) (hi := (503498849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((3309 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(3309 / 2000) = 1/(2000 / 3309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15759 : Bounds (15734339 / 31250000) (503498849 / 1000000000) (Real.log (3309 / 2000)) := by
  have h := reflection_log_15759_neg
  have he : Real.log (3309 / 2000) = -Real.log (2000 / 3309) := by
    rw [show ((3309 / 2000) : ℝ) = ((2000 / 3309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15760_neg : (212552527 / 200000000) ≤ -Real.log (691 / 2000) ∧
    -Real.log (691 / 2000) ≤ (1062762637 / 1000000000) := by
  have h := checkLog_sound (w := (309 / 1691)) (n := 12)
    (lo := (73923091 / 200000000)) (hi := (11550483 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 691) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(1000 / 691) = 1/(691 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15760 : Bounds (-1062762637 / 1000000000) (-212552527 / 200000000) (Real.log (691 / 2000)) := by
  have h := reflection_log_15760_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15761_neg : (504096433 / 1000000000) ≤ -Real.log (1000000 / 1655489) ∧
    -Real.log (1000000 / 1655489) ≤ (252048217 / 500000000) := by
  have h := checkLog_sound (w := (655489 / 2655489)) (n := 12)
    (lo := (504096433 / 1000000000)) (hi := (252048217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655489 / 1000000) = 1/(1000000 / 1655489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15761 : Bounds (504096433 / 1000000000) (252048217 / 500000000) (Real.log (1655489 / 1000000)) := by
  have h := reflection_log_15761_neg
  have he : Real.log (1655489 / 1000000) = -Real.log (1000000 / 1655489) := by
    rw [show ((1655489 / 1000000) : ℝ) = ((1000000 / 1655489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15762_neg : (532814629 / 500000000) ≤ -Real.log (344511 / 1000000) ∧
    -Real.log (344511 / 1000000) ≤ (53281463 / 50000000) := by
  have h := checkLog_sound (w := (155489 / 844511)) (n := 12)
    (lo := (186241039 / 500000000)) (hi := (372482079 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344511) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344511) = 1/(344511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15762 : Bounds (-53281463 / 50000000) (-532814629 / 500000000) (Real.log (344511 / 1000000)) := by
  have h := reflection_log_15762_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15763_neg : (22461313 / 40000000) ≤ -Real.log (570334170879 / 1000000000000) ∧
    -Real.log (570334170879 / 1000000000000) ≤ (280766413 / 500000000) := by
  have h := checkLog_sound (w := (429665829121 / 1570334170879)) (n := 12)
    (lo := (22461313 / 40000000)) (hi := (280766413 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 570334170879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 570334170879) = 1/(570334170879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15763 : Bounds (-280766413 / 500000000) (-22461313 / 40000000) (Real.log (570334170879 / 1000000000000)) := by
  have h := reflection_log_15763_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15764_neg : (559263787 / 1000000000) ≤ -Real.log (2286519 / 4000000) ∧
    -Real.log (2286519 / 4000000) ≤ (139815947 / 250000000) := by
  have h := checkLog_sound (w := (1713481 / 6286519)) (n := 12)
    (lo := (559263787 / 1000000000)) (hi := (139815947 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4000000 / 2286519) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4000000 / 2286519) = 1/(2286519 / 4000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15764 : Bounds (-139815947 / 250000000) (-559263787 / 1000000000) (Real.log (2286519 / 4000000)) := by
  have h := reflection_log_15764_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15765_neg : (1566261483 / 1000000000) ≤ -Real.log (125000000000 / 598589001447) ∧
    -Real.log (125000000000 / 598589001447) ≤ (783130743 / 500000000) := by
  have h := checkLog_sound (w := (98589001447 / 1098589001447)) (n := 12)
    (lo := (179967123 / 1000000000)) (hi := (44991781 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((598589001447 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(598589001447 / 500000000000) = 1/(125000000000 / 598589001447) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15765 : Bounds (1566261483 / 1000000000) (783130743 / 500000000) (Real.log (598589001447 / 125000000000)) := by
  have h := reflection_log_15765_neg
  have he : Real.log (598589001447 / 125000000000) = -Real.log (125000000000 / 598589001447) := by
    rw [show ((598589001447 / 125000000000) : ℝ) = ((125000000000 / 598589001447) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15766_neg : (1569725691 / 1000000000) ≤ -Real.log (500000000000 / 2402664936679) ∧
    -Real.log (500000000000 / 2402664936679) ≤ (784862847 / 500000000) := by
  have h := checkLog_sound (w := (402664936679 / 4402664936679)) (n := 12)
    (lo := (183431331 / 1000000000)) (hi := (45857833 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2402664936679 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2402664936679 / 2000000000000) = 1/(500000000000 / 2402664936679) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15766 : Bounds (1569725691 / 1000000000) (784862847 / 500000000) (Real.log (2402664936679 / 500000000000)) := by
  have h := reflection_log_15766_neg
  have he : Real.log (2402664936679 / 500000000000) = -Real.log (500000000000 / 2402664936679) := by
    rw [show ((2402664936679 / 500000000000) : ℝ) = ((500000000000 / 2402664936679) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15767_neg : (7012215383 / 1000000000) ≤ -Real.log (125000000000 / 138763888888889) ∧
    -Real.log (125000000000 / 138763888888889) ≤ (3506107697 / 500000000) := by
  have h := checkLog_sound (w := (10763888888889 / 266763888888889)) (n := 12)
    (lo := (80743583 / 1000000000)) (hi := (2523237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((138763888888889 / 128000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(138763888888889 / 128000000000000) = 1/(125000000000 / 138763888888889) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15767 : Bounds (7012215383 / 1000000000) (3506107697 / 500000000) (Real.log (138763888888889 / 125000000000)) := by
  have h := reflection_log_15767_neg
  have he : Real.log (138763888888889 / 125000000000) = -Real.log (125000000000 / 138763888888889) := by
    rw [show ((138763888888889 / 125000000000) : ℝ) = ((125000000000 / 138763888888889) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15768_neg : (34617343 / 50000000) ≤ -Real.log (625 / 1249) ∧
    -Real.log (625 / 1249) ≤ (692346861 / 1000000000) := by
  have h := checkLog_sound (w := (312 / 937)) (n := 12)
    (lo := (34617343 / 50000000)) (hi := (692346861 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 625) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1249 / 625) = 1/(625 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15768 : Bounds (34617343 / 50000000) (692346861 / 1000000000) (Real.log (1249 / 625)) := by
  have h := reflection_log_15768_neg
  have he : Real.log (1249 / 625) = -Real.log (625 / 1249) := by
    rw [show ((1249 / 625) : ℝ) = ((625 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15769_neg : (1609437911 / 250000000) ≤ -Real.log (1 / 625) ∧
    -Real.log (1 / 625) ≤ (3218875827 / 500000000) := by
  have h := checkLog_sound (w := (113 / 1137)) (n := 12)
    (lo := (12464189 / 62500000)) (hi := (7977081 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 512) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 512) = 1/(1 / 625) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15769 : Bounds (-3218875827 / 500000000) (-1609437911 / 250000000) (Real.log (1 / 625)) := by
  have h := reflection_log_15769_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15770_neg : (997901 / 1000000000) ≤ -Real.log (78125 / 78203) ∧
    -Real.log (78125 / 78203) ≤ (498951 / 500000000) := by
  have h := checkLog_sound (w := (39 / 78164)) (n := 12)
    (lo := (997901 / 1000000000)) (hi := (498951 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78203 / 78125) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78203 / 78125) = 1/(78125 / 78203) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15770 : Bounds (997901 / 1000000000) (498951 / 500000000) (Real.log (78203 / 78125)) := by
  have h := reflection_log_15770_neg
  have he : Real.log (78203 / 78125) = -Real.log (78125 / 78203) := by
    rw [show ((78203 / 78125) : ℝ) = ((78125 / 78203) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15771_neg : (499449 / 500000000) ≤ -Real.log (78047 / 78125) ∧
    -Real.log (78047 / 78125) ≤ (998899 / 1000000000) := by
  have h := checkLog_sound (w := (39 / 78086)) (n := 12)
    (lo := (499449 / 500000000)) (hi := (998899 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((78125 / 78047) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(78125 / 78047) = 1/(78047 / 78125) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15771 : Bounds (-998899 / 1000000000) (-499449 / 500000000) (Real.log (78047 / 78125)) := by
  have h := reflection_log_15771_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15772_neg : (503721851 / 1000000000) ≤ -Real.log (1000000 / 1654869) ∧
    -Real.log (1000000 / 1654869) ≤ (125930463 / 250000000) := by
  have h := checkLog_sound (w := (654869 / 2654869)) (n := 12)
    (lo := (503721851 / 1000000000)) (hi := (125930463 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1654869 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1654869 / 1000000) = 1/(1000000 / 1654869) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15772 : Bounds (503721851 / 1000000000) (125930463 / 250000000) (Real.log (1654869 / 1000000)) := by
  have h := reflection_log_15772_neg
  have he : Real.log (1654869 / 1000000) = -Real.log (1000000 / 1654869) := by
    rw [show ((1654869 / 1000000) : ℝ) = ((1000000 / 1654869) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15773_neg : (1063831223 / 1000000000) ≤ -Real.log (345131 / 1000000) ∧
    -Real.log (345131 / 1000000) ≤ (42553249 / 40000000) := by
  have h := checkLog_sound (w := (154869 / 845131)) (n := 12)
    (lo := (370684043 / 1000000000)) (hi := (92671011 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 345131) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 345131) = 1/(345131 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15773 : Bounds (-42553249 / 40000000) (-1063831223 / 1000000000) (Real.log (345131 / 1000000)) := by
  have h := reflection_log_15773_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15774_neg : (504322323 / 1000000000) ≤ -Real.log (1000000 / 1655863) ∧
    -Real.log (1000000 / 1655863) ≤ (126080581 / 250000000) := by
  have h := checkLog_sound (w := (655863 / 2655863)) (n := 12)
    (lo := (504322323 / 1000000000)) (hi := (126080581 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1655863 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1655863 / 1000000) = 1/(1000000 / 1655863) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15774 : Bounds (504322323 / 1000000000) (126080581 / 250000000) (Real.log (1655863 / 1000000)) := by
  have h := reflection_log_15774_neg
  have he : Real.log (1655863 / 1000000) = -Real.log (1000000 / 1655863) := by
    rw [show ((1655863 / 1000000) : ℝ) = ((1000000 / 1655863) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15775_neg : (266678861 / 250000000) ≤ -Real.log (344137 / 1000000) ∧
    -Real.log (344137 / 1000000) ≤ (533357723 / 500000000) := by
  have h := checkLog_sound (w := (155863 / 844137)) (n := 12)
    (lo := (46696033 / 125000000)) (hi := (74713653 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 344137) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 344137) = 1/(344137 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15775 : Bounds (-533357723 / 500000000) (-266678861 / 250000000) (Real.log (344137 / 1000000)) := by
  have h := reflection_log_15775_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15776_neg : (281196561 / 500000000) ≤ -Real.log (569843725231 / 1000000000000) ∧
    -Real.log (569843725231 / 1000000000000) ≤ (562393123 / 1000000000) := by
  have h := checkLog_sound (w := (430156274769 / 1569843725231)) (n := 12)
    (lo := (281196561 / 500000000)) (hi := (562393123 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 569843725231) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 569843725231) = 1/(569843725231 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15776 : Bounds (-562393123 / 1000000000) (-281196561 / 500000000) (Real.log (569843725231 / 1000000000000)) := by
  have h := reflection_log_15776_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15777_neg : (140027343 / 250000000) ≤ -Real.log (571146592839 / 1000000000000) ∧
    -Real.log (571146592839 / 1000000000000) ≤ (560109373 / 1000000000) := by
  have h := checkLog_sound (w := (428853407161 / 1571146592839)) (n := 12)
    (lo := (140027343 / 250000000)) (hi := (560109373 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 571146592839) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 571146592839) = 1/(571146592839 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15777 : Bounds (-560109373 / 1000000000) (-140027343 / 250000000) (Real.log (571146592839 / 1000000000000)) := by
  have h := reflection_log_15777_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15778_neg : (783776537 / 500000000) ≤ -Real.log (20000000000 / 95898021331) ∧
    -Real.log (20000000000 / 95898021331) ≤ (1567553077 / 1000000000) := by
  have h := checkLog_sound (w := (15898021331 / 175898021331)) (n := 12)
    (lo := (90629357 / 500000000)) (hi := (36251743 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((95898021331 / 80000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(95898021331 / 80000000000) = 1/(20000000000 / 95898021331) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15778 : Bounds (783776537 / 500000000) (1567553077 / 1000000000) (Real.log (95898021331 / 20000000000)) := by
  have h := reflection_log_15778_neg
  have he : Real.log (95898021331 / 20000000000) = -Real.log (20000000000 / 95898021331) := by
    rw [show ((95898021331 / 20000000000) : ℝ) = ((20000000000 / 95898021331) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15779_neg : (1571037767 / 1000000000) ≤ -Real.log (250000000000 / 1202909742341) ∧
    -Real.log (250000000000 / 1202909742341) ≤ (157103777 / 100000000) := by
  have h := checkLog_sound (w := (202909742341 / 2202909742341)) (n := 12)
    (lo := (184743407 / 1000000000)) (hi := (11546463 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1202909742341 / 1000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(1202909742341 / 1000000000000) = 1/(250000000000 / 1202909742341) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15779 : Bounds (1571037767 / 1000000000) (157103777 / 100000000) (Real.log (1202909742341 / 250000000000)) := by
  have h := reflection_log_15779_neg
  have he : Real.log (1202909742341 / 250000000000) = -Real.log (250000000000 / 1202909742341) := by
    rw [show ((1202909742341 / 250000000000) : ℝ) = ((250000000000 / 1202909742341) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15780_neg : (7012215383 / 1000000000) ≤ -Real.log (100000000000 / 111011111111111) ∧
    -Real.log (100000000000 / 111011111111111) ≤ (3506107697 / 500000000) := by
  have h := checkLog_sound (w := (8611111111111 / 213411111111111)) (n := 12)
    (lo := (80743583 / 1000000000)) (hi := (2523237 / 31250000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((111011111111111 / 102400000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(111011111111111 / 102400000000000) = 1/(100000000000 / 111011111111111) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15780 : Bounds (7012215383 / 1000000000) (3506107697 / 500000000) (Real.log (111011111111111 / 100000000000)) := by
  have h := reflection_log_15780_neg
  have he : Real.log (111011111111111 / 100000000000) = -Real.log (100000000000 / 111011111111111) := by
    rw [show ((111011111111111 / 100000000000) : ℝ) = ((100000000000 / 111011111111111) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15781_neg : (891262313 / 125000000) ≤ -Real.log (1 / 1249) ∧
    -Real.log (1 / 1249) ≤ (1426019703 / 200000000) := by
  have h := checkLog_sound (w := (225 / 2273)) (n := 12)
    (lo := (12414169 / 62500000)) (hi := (39725341 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1249 / 1024) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(1249 / 1024) = 1/(1 / 1249) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15781 : Bounds (891262313 / 125000000) (1426019703 / 200000000) (Real.log (1249 / 1)) := by
  have h := reflection_log_15781_neg
  have he : Real.log (1249 / 1) = -Real.log (1 / 1249) := by
    rw [show ((1249 / 1) : ℝ) = ((1 / 1249) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15782_neg : (138489387 / 200000000) ≤ -Real.log (5000 / 9993) ∧
    -Real.log (5000 / 9993) ≤ (86555867 / 125000000) := by
  have h := checkLog_sound (w := (4993 / 14993)) (n := 12)
    (lo := (138489387 / 200000000)) (hi := (86555867 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((9993 / 5000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(9993 / 5000) = 1/(5000 / 9993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15782 : Bounds (138489387 / 200000000) (86555867 / 125000000) (Real.log (9993 / 5000)) := by
  have h := reflection_log_15782_neg
  have he : Real.log (9993 / 5000) = -Real.log (5000 / 9993) := by
    rw [show ((9993 / 5000) : ℝ) = ((5000 / 9993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15783_neg : (6571283037 / 1000000000) ≤ -Real.log (7 / 5000) ∧
    -Real.log (7 / 5000) ≤ (6571283047 / 1000000000) := by
  have h := checkLog_sound (w := (177 / 1073)) (n := 12)
    (lo := (332958417 / 1000000000)) (hi := (166479209 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 448) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 448) = 1/(7 / 5000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15783 : Bounds (-6571283047 / 1000000000) (-6571283037 / 1000000000) (Real.log (7 / 5000)) := by
  have h := reflection_log_15783_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15784_neg : (998101 / 1000000000) ≤ -Real.log (5000000 / 5004993) ∧
    -Real.log (5000000 / 5004993) ≤ (499051 / 500000000) := by
  have h := checkLog_sound (w := (4993 / 10004993)) (n := 12)
    (lo := (998101 / 1000000000)) (hi := (499051 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5004993 / 5000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5004993 / 5000000) = 1/(5000000 / 5004993) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15784 : Bounds (998101 / 1000000000) (499051 / 500000000) (Real.log (5004993 / 5000000)) := by
  have h := reflection_log_15784_neg
  have he : Real.log (5004993 / 5000000) = -Real.log (5000000 / 5004993) := by
    rw [show ((5004993 / 5000000) : ℝ) = ((5000000 / 5004993) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15785_neg : (499549 / 500000000) ≤ -Real.log (4995007 / 5000000) ∧
    -Real.log (4995007 / 5000000) ≤ (999099 / 1000000000) := by
  have h := checkLog_sound (w := (4993 / 9995007)) (n := 12)
    (lo := (499549 / 500000000)) (hi := (999099 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((5000000 / 4995007) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(5000000 / 4995007) = 1/(4995007 / 5000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15785 : Bounds (-999099 / 1000000000) (-499549 / 500000000) (Real.log (4995007 / 5000000)) := by
  have h := reflection_log_15785_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15786_neg : (503948429 / 1000000000) ≤ -Real.log (250000 / 413811) ∧
    -Real.log (250000 / 413811) ≤ (50394843 / 100000000) := by
  have h := checkLog_sound (w := (163811 / 663811)) (n := 12)
    (lo := (503948429 / 1000000000)) (hi := (50394843 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((413811 / 250000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(413811 / 250000) = 1/(250000 / 413811) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15786 : Bounds (503948429 / 1000000000) (50394843 / 100000000) (Real.log (413811 / 250000)) := by
  have h := reflection_log_15786_neg
  have he : Real.log (413811 / 250000) = -Real.log (250000 / 413811) := by
    rw [show ((413811 / 250000) : ℝ) = ((250000 / 413811) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15787_neg : (1064918357 / 1000000000) ≤ -Real.log (86189 / 250000) ∧
    -Real.log (86189 / 250000) ≤ (1064918359 / 1000000000) := by
  have h := checkLog_sound (w := (38811 / 211189)) (n := 12)
    (lo := (371771177 / 1000000000)) (hi := (185885589 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((125000 / 86189) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(125000 / 86189) = 1/(86189 / 250000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15787 : Bounds (-1064918359 / 1000000000) (-1064918357 / 1000000000) (Real.log (86189 / 250000)) := by
  have h := reflection_log_15787_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15788_neg : (63068973 / 125000000) ≤ -Real.log (1000000 / 1656243) ∧
    -Real.log (1000000 / 1656243) ≤ (100910357 / 200000000) := by
  have h := checkLog_sound (w := (656243 / 2656243)) (n := 12)
    (lo := (63068973 / 125000000)) (hi := (100910357 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1656243 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1656243 / 1000000) = 1/(1000000 / 1656243) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15788 : Bounds (63068973 / 125000000) (100910357 / 200000000) (Real.log (1656243 / 1000000)) := by
  have h := reflection_log_15788_neg
  have he : Real.log (1656243 / 1000000) = -Real.log (1000000 / 1656243) := by
    rw [show ((1656243 / 1000000) : ℝ) = ((1000000 / 1656243) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15789_neg : (533910133 / 500000000) ≤ -Real.log (343757 / 1000000) ∧
    -Real.log (343757 / 1000000) ≤ (266955067 / 250000000) := by
  have h := checkLog_sound (w := (156243 / 843757)) (n := 12)
    (lo := (187336543 / 500000000)) (hi := (374673087 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343757) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 343757) = 1/(343757 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15789 : Bounds (-266955067 / 250000000) (-533910133 / 500000000) (Real.log (343757 / 1000000)) := by
  have h := reflection_log_15789_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15790_neg : (281634241 / 500000000) ≤ -Real.log (569345124951 / 1000000000000) ∧
    -Real.log (569345124951 / 1000000000000) ≤ (563268483 / 1000000000) := by
  have h := checkLog_sound (w := (430654875049 / 1569345124951)) (n := 12)
    (lo := (281634241 / 500000000)) (hi := (563268483 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 569345124951) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 569345124951) = 1/(569345124951 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15790 : Bounds (-563268483 / 1000000000) (-281634241 / 500000000) (Real.log (569345124951 / 1000000000000)) := by
  have h := reflection_log_15790_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15791_neg : (70121241 / 125000000) ≤ -Real.log (35665956279 / 62500000000) ∧
    -Real.log (35665956279 / 62500000000) ≤ (560969929 / 1000000000) := by
  have h := checkLog_sound (w := (26834043721 / 98165956279)) (n := 12)
    (lo := (70121241 / 125000000)) (hi := (560969929 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500000000 / 35665956279) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(62500000000 / 35665956279) = 1/(35665956279 / 62500000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15791 : Bounds (-560969929 / 1000000000) (-70121241 / 125000000) (Real.log (35665956279 / 62500000000)) := by
  have h := reflection_log_15791_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15792_neg : (1568866787 / 1000000000) ≤ -Real.log (500000000000 / 2400602165009) ∧
    -Real.log (500000000000 / 2400602165009) ≤ (156886679 / 100000000) := by
  have h := checkLog_sound (w := (400602165009 / 4400602165009)) (n := 12)
    (lo := (182572427 / 1000000000)) (hi := (45643107 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2400602165009 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2400602165009 / 2000000000000) = 1/(500000000000 / 2400602165009) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15792 : Bounds (1568866787 / 1000000000) (156886679 / 100000000) (Real.log (2400602165009 / 500000000000)) := by
  have h := reflection_log_15792_neg
  have he : Real.log (2400602165009 / 500000000000) = -Real.log (500000000000 / 2400602165009) := by
    rw [show ((2400602165009 / 500000000000) : ℝ) = ((500000000000 / 2400602165009) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15793_neg : (1572372049 / 1000000000) ≤ -Real.log (125000000000 / 602257917657) ∧
    -Real.log (125000000000 / 602257917657) ≤ (393093013 / 250000000) := by
  have h := checkLog_sound (w := (102257917657 / 1102257917657)) (n := 12)
    (lo := (186077689 / 1000000000)) (hi := (18607769 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((602257917657 / 500000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(602257917657 / 500000000000) = 1/(125000000000 / 602257917657) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15793 : Bounds (1572372049 / 1000000000) (393093013 / 250000000) (Real.log (602257917657 / 125000000000)) := by
  have h := reflection_log_15793_neg
  have he : Real.log (602257917657 / 125000000000) = -Real.log (125000000000 / 602257917657) := by
    rw [show ((602257917657 / 125000000000) : ℝ) = ((125000000000 / 602257917657) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15794_neg : (1815932493 / 250000000) ≤ -Real.log (100000000000 / 142757142857143) ∧
    -Real.log (100000000000 / 142757142857143) ≤ (7263729983 / 1000000000) := by
  have h := checkLog_sound (w := (40357142857143 / 245157142857143)) (n := 12)
    (lo := (83064543 / 250000000)) (hi := (332258173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((142757142857143 / 102400000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(142757142857143 / 102400000000000) = 1/(100000000000 / 142757142857143) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15794 : Bounds (1815932493 / 250000000) (7263729983 / 1000000000) (Real.log (142757142857143 / 100000000000)) := by
  have h := reflection_log_15794_neg
  have he : Real.log (142757142857143 / 100000000000) = -Real.log (100000000000 / 142757142857143) := by
    rw [show ((142757142857143 / 100000000000) : ℝ) = ((100000000000 / 142757142857143) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15795_neg : (692547 / 1000000) ≤ -Real.log (2500 / 4997) ∧
    -Real.log (2500 / 4997) ≤ (692547001 / 1000000000) := by
  have h := checkLog_sound (w := (2497 / 7497)) (n := 12)
    (lo := (692547 / 1000000)) (hi := (692547001 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((4997 / 2500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(4997 / 2500) = 1/(2500 / 4997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15795 : Bounds (692547 / 1000000) (692547001 / 1000000000) (Real.log (4997 / 2500)) := by
  have h := reflection_log_15795_neg
  have he : Real.log (4997 / 2500) = -Real.log (2500 / 4997) := by
    rw [show ((4997 / 2500) : ℝ) = ((2500 / 4997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15796_neg : (6725433717 / 1000000000) ≤ -Real.log (3 / 2500) ∧
    -Real.log (3 / 2500) ≤ (6725433727 / 1000000000) := by
  have h := checkLog_sound (w := (241 / 1009)) (n := 12)
    (lo := (487109097 / 1000000000)) (hi := (243554549 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((625 / 384) : ℝ) 9 (by norm_num)
  have hq : (2 : ℝ)^9*(625 / 384) = 1/(3 / 2500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15796 : Bounds (-6725433727 / 1000000000) (-6725433717 / 1000000000) (Real.log (3 / 2500)) := by
  have h := reflection_log_15796_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15797_neg : (998301 / 1000000000) ≤ -Real.log (2500000 / 2502497) ∧
    -Real.log (2500000 / 2502497) ≤ (499151 / 500000000) := by
  have h := checkLog_sound (w := (2497 / 5002497)) (n := 12)
    (lo := (998301 / 1000000000)) (hi := (499151 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2502497 / 2500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2502497 / 2500000) = 1/(2500000 / 2502497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15797 : Bounds (998301 / 1000000000) (499151 / 500000000) (Real.log (2502497 / 2500000)) := by
  have h := reflection_log_15797_neg
  have he : Real.log (2502497 / 2500000) = -Real.log (2500000 / 2502497) := by
    rw [show ((2502497 / 2500000) : ℝ) = ((2500000 / 2502497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15798_neg : (999299 / 1000000000) ≤ -Real.log (2497503 / 2500000) ∧
    -Real.log (2497503 / 2500000) ≤ (9993 / 10000000) := by
  have h := checkLog_sound (w := (2497 / 4997503)) (n := 12)
    (lo := (999299 / 1000000000)) (hi := (9993 / 10000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2500000 / 2497503) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2500000 / 2497503) = 1/(2497503 / 2500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15798 : Bounds (-9993 / 10000000) (-999299 / 1000000000) (Real.log (2497503 / 2500000)) := by
  have h := reflection_log_15798_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15799_neg : (504177977 / 1000000000) ≤ -Real.log (125000 / 206953) ∧
    -Real.log (125000 / 206953) ≤ (252088989 / 500000000) := by
  have h := checkLog_sound (w := (81953 / 331953)) (n := 12)
    (lo := (504177977 / 1000000000)) (hi := (252088989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((206953 / 125000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(206953 / 125000) = 1/(125000 / 206953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15799 : Bounds (504177977 / 1000000000) (252088989 / 500000000) (Real.log (206953 / 125000)) := by
  have h := reflection_log_15799_neg
  have he : Real.log (206953 / 125000) = -Real.log (125000 / 206953) := by
    rw [show ((206953 / 125000) : ℝ) = ((125000 / 206953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15800_neg : (533010597 / 500000000) ≤ -Real.log (43047 / 125000) ∧
    -Real.log (43047 / 125000) ≤ (266505299 / 250000000) := by
  have h := checkLog_sound (w := (19453 / 105547)) (n := 12)
    (lo := (186437007 / 500000000)) (hi := (74574803 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((62500 / 43047) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(62500 / 43047) = 1/(43047 / 125000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15800 : Bounds (-266505299 / 250000000) (-533010597 / 500000000) (Real.log (43047 / 125000)) := by
  have h := reflection_log_15800_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15801_neg : (252392407 / 500000000) ≤ -Real.log (1000000 / 1656629) ∧
    -Real.log (1000000 / 1656629) ≤ (100956963 / 200000000) := by
  have h := checkLog_sound (w := (656629 / 2656629)) (n := 12)
    (lo := (252392407 / 500000000)) (hi := (100956963 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1656629 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1656629 / 1000000) = 1/(1000000 / 1656629) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15801 : Bounds (252392407 / 500000000) (100956963 / 200000000) (Real.log (1656629 / 1000000)) := by
  have h := reflection_log_15801_neg
  have he : Real.log (1656629 / 1000000) = -Real.log (1000000 / 1656629) := by
    rw [show ((1656629 / 1000000) : ℝ) = ((1000000 / 1656629) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15802_neg : (1068943783 / 1000000000) ≤ -Real.log (343371 / 1000000) ∧
    -Real.log (343371 / 1000000) ≤ (213788757 / 200000000) := by
  have h := checkLog_sound (w := (156629 / 843371)) (n := 12)
    (lo := (375796603 / 1000000000)) (hi := (93949151 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 343371) : ℝ) 1 (by norm_num)
  have hq : (2 : ℝ)^1*(500000 / 343371) = 1/(343371 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15802 : Bounds (-213788757 / 200000000) (-1068943783 / 1000000000) (Real.log (343371 / 1000000)) := by
  have h := reflection_log_15802_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15803_neg : (70519871 / 125000000) ≤ -Real.log (568838356359 / 1000000000000) ∧
    -Real.log (568838356359 / 1000000000000) ≤ (564158969 / 1000000000) := by
  have h := checkLog_sound (w := (431161643641 / 1568838356359)) (n := 12)
    (lo := (70519871 / 125000000)) (hi := (564158969 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 568838356359) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 568838356359) = 1/(568838356359 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15803 : Bounds (-564158969 / 1000000000) (-70519871 / 125000000) (Real.log (568838356359 / 1000000000000)) := by
  have h := reflection_log_15803_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15804_neg : (280921609 / 500000000) ≤ -Real.log (8908705791 / 15625000000) ∧
    -Real.log (8908705791 / 15625000000) ≤ (561843219 / 1000000000) := by
  have h := checkLog_sound (w := (6716294209 / 24533705791)) (n := 12)
    (lo := (280921609 / 500000000)) (hi := (561843219 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((15625000000 / 8908705791) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(15625000000 / 8908705791) = 1/(8908705791 / 15625000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15804 : Bounds (-561843219 / 1000000000) (-280921609 / 500000000) (Real.log (8908705791 / 15625000000)) := by
  have h := reflection_log_15804_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_15805_neg : (1570199171 / 1000000000) ≤ -Real.log (500000000000 / 2403802820173) ∧
    -Real.log (500000000000 / 2403802820173) ≤ (785099587 / 500000000) := by
  have h := checkLog_sound (w := (403802820173 / 4403802820173)) (n := 12)
    (lo := (183904811 / 1000000000)) (hi := (45976203 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2403802820173 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2403802820173 / 2000000000000) = 1/(500000000000 / 2403802820173) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15805 : Bounds (1570199171 / 1000000000) (785099587 / 500000000) (Real.log (2403802820173 / 500000000000)) := by
  have h := reflection_log_15805_neg
  have he : Real.log (2403802820173 / 500000000000) = -Real.log (500000000000 / 2403802820173) := by
    rw [show ((2403802820173 / 500000000000) : ℝ) = ((500000000000 / 2403802820173) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15806_neg : (1573728597 / 1000000000) ≤ -Real.log (500000000000 / 2412301854263) ∧
    -Real.log (500000000000 / 2412301854263) ≤ (7868643 / 5000000) := by
  have h := checkLog_sound (w := (412301854263 / 4412301854263)) (n := 12)
    (lo := (187434237 / 1000000000)) (hi := (93717119 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2412301854263 / 2000000000000) : ℝ) 2 (by norm_num)
  have hq : (2 : ℝ)^2*(2412301854263 / 2000000000000) = 1/(500000000000 / 2412301854263) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15806 : Bounds (1573728597 / 1000000000) (7868643 / 5000000) (Real.log (2412301854263 / 500000000000)) := by
  have h := reflection_log_15806_neg
  have he : Real.log (2412301854263 / 500000000000) = -Real.log (500000000000 / 2412301854263) := by
    rw [show ((2412301854263 / 500000000000) : ℝ) = ((500000000000 / 2412301854263) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_15807_neg : (1815932493 / 250000000) ≤ -Real.log (250000000000 / 356892857142857) ∧
    -Real.log (250000000000 / 356892857142857) ≤ (7263729983 / 1000000000) := by
  have h := checkLog_sound (w := (100892857142857 / 612892857142857)) (n := 12)
    (lo := (83064543 / 250000000)) (hi := (332258173 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((356892857142857 / 256000000000000) : ℝ) 10 (by norm_num)
  have hq : (2 : ℝ)^10*(356892857142857 / 256000000000000) = 1/(250000000000 / 356892857142857) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_15807 : Bounds (1815932493 / 250000000) (7263729983 / 1000000000) (Real.log (356892857142857 / 250000000000)) := by
  have h := reflection_log_15807_neg
  have he : Real.log (356892857142857 / 250000000000) = -Real.log (250000000000 / 356892857142857) := by
    rw [show ((356892857142857 / 250000000000) : ℝ) = ((250000000000 / 356892857142857) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


