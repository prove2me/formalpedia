-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q00
-- name    : CK_GeneralCK_Certificates_Generated_LowRatioFamily_Logs0114__3_q00
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-29T10:20:43.807202+00:00
-- url     : https://prove2.me/theorems/fad1fd28-8ccb-4657-9807-9d51811c0445
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generat…
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 1 of 3)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 1 of 3)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 (+2 modules: GeneralCK.Certificates.Generated.LowRatioFamily.Logs0115, GeneralCK.Certificates.Generated.LowRatioFamily.Logs0116) (piece 1 of 3) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/Generated/LowRatioFamily/Logs0114 (+2 modules: GeneralCK/Certificates/Generated/LowRatioFamily/Logs0115, GeneralCK/Certificates/Generated/LowRatioFamily/Logs0116) (piece 1 of 3).lean)

import Definitions.Def_CK_GeneralCK_Certificates_LowRatioFamilyHelpers

-- ===== source module GeneralCK.Certificates.Generated.LowRatioFamily.Logs0114 =====
section
namespace GeneralCK.Certificates.LowRatioFamily
open GeneralCK.Certificates.Reflection GeneralCK.Reflection.SmallRatio
open GeneralCK.Certificates.Mixed
theorem reflection_log_7296_neg : (112619017 / 1000000000) ≤ -Real.log (893491 / 1000000) ∧
    -Real.log (893491 / 1000000) ≤ (56309509 / 500000000) := by
  have h := checkLog_sound (w := (106509 / 1893491)) (n := 12)
    (lo := (112619017 / 1000000000)) (hi := (56309509 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 893491) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 893491) = 1/(893491 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7296 : Bounds (-56309509 / 500000000) (-112619017 / 1000000000) (Real.log (893491 / 1000000)) := by
  have h := reflection_log_7296_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7297_neg : (101631973 / 1000000000) ≤ -Real.log (31250 / 34593) ∧
    -Real.log (31250 / 34593) ≤ (50815987 / 500000000) := by
  have h := checkLog_sound (w := (3343 / 65843)) (n := 12)
    (lo := (101631973 / 1000000000)) (hi := (50815987 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((34593 / 31250) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(34593 / 31250) = 1/(31250 / 34593) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7297 : Bounds (101631973 / 1000000000) (50815987 / 500000000) (Real.log (34593 / 31250)) := by
  have h := reflection_log_7297_neg
  have he : Real.log (34593 / 31250) = -Real.log (31250 / 34593) := by
    rw [show ((34593 / 31250) : ℝ) = ((31250 / 34593) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7298_neg : (56570911 / 500000000) ≤ -Real.log (27907 / 31250) ∧
    -Real.log (27907 / 31250) ≤ (113141823 / 1000000000) := by
  have h := checkLog_sound (w := (3343 / 59157)) (n := 12)
    (lo := (56570911 / 500000000)) (hi := (113141823 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((31250 / 27907) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(31250 / 27907) = 1/(27907 / 31250) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7298 : Bounds (-113141823 / 1000000000) (-56570911 / 500000000) (Real.log (27907 / 31250)) := by
  have h := reflection_log_7298_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7299_neg : (11509849 / 1000000000) ≤ -Real.log (965386851 / 976562500) ∧
    -Real.log (965386851 / 976562500) ≤ (230197 / 20000000) := by
  have h := checkLog_sound (w := (11175649 / 1941949351)) (n := 12)
    (lo := (11509849 / 1000000000)) (hi := (230197 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((976562500 / 965386851) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(976562500 / 965386851) = 1/(965386851 / 976562500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7299 : Bounds (-230197 / 20000000) (-11509849 / 1000000000) (Real.log (965386851 / 976562500)) := by
  have h := reflection_log_7299_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7300_neg : (5704501 / 500000000) ≤ -Real.log (988655832919 / 1000000000000) ∧
    -Real.log (988655832919 / 1000000000000) ≤ (11409003 / 1000000000) := by
  have h := checkLog_sound (w := (11344167081 / 1988655832919)) (n := 12)
    (lo := (5704501 / 500000000)) (hi := (11409003 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988655832919) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988655832919) = 1/(988655832919 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7300 : Bounds (-11409003 / 1000000000) (-5704501 / 500000000) (Real.log (988655832919 / 1000000000000)) := by
  have h := reflection_log_7300_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7301_neg : (213829031 / 1000000000) ≤ -Real.log (15625000000 / 19350170427) ∧
    -Real.log (15625000000 / 19350170427) ≤ (26728629 / 125000000) := by
  have h := checkLog_sound (w := (3725170427 / 34975170427)) (n := 12)
    (lo := (213829031 / 1000000000)) (hi := (26728629 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((19350170427 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(19350170427 / 15625000000) = 1/(15625000000 / 19350170427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7301 : Bounds (213829031 / 1000000000) (26728629 / 125000000) (Real.log (19350170427 / 15625000000)) := by
  have h := reflection_log_7301_neg
  have he : Real.log (19350170427 / 15625000000) = -Real.log (15625000000 / 19350170427) := by
    rw [show ((19350170427 / 15625000000) : ℝ) = ((15625000000 / 19350170427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7302_neg : (53693449 / 250000000) ≤ -Real.log (125000000000 / 154947683377) ∧
    -Real.log (125000000000 / 154947683377) ≤ (214773797 / 1000000000) := by
  have h := checkLog_sound (w := (29947683377 / 279947683377)) (n := 12)
    (lo := (53693449 / 250000000)) (hi := (214773797 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154947683377 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154947683377 / 125000000000) = 1/(125000000000 / 154947683377) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7302 : Bounds (53693449 / 250000000) (214773797 / 1000000000) (Real.log (154947683377 / 125000000000)) := by
  have h := reflection_log_7302_neg
  have he : Real.log (154947683377 / 125000000000) = -Real.log (125000000000 / 154947683377) := by
    rw [show ((154947683377 / 125000000000) : ℝ) = ((125000000000 / 154947683377) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7303_neg : (429482133 / 1000000000) ≤ -Real.log (62500000000 / 96028852251) ∧
    -Real.log (62500000000 / 96028852251) ≤ (214741067 / 500000000) := by
  have h := checkLog_sound (w := (33528852251 / 158528852251)) (n := 12)
    (lo := (429482133 / 1000000000)) (hi := (214741067 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((96028852251 / 62500000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(96028852251 / 62500000000) = 1/(62500000000 / 96028852251) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7303 : Bounds (429482133 / 1000000000) (214741067 / 500000000) (Real.log (96028852251 / 62500000000)) := by
  have h := reflection_log_7303_neg
  have he : Real.log (96028852251 / 62500000000) = -Real.log (62500000000 / 96028852251) := by
    rw [show ((96028852251 / 62500000000) : ℝ) = ((62500000000 / 96028852251) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7304_neg : (107632269 / 250000000) ≤ -Real.log (100000000000 / 153807106599) ∧
    -Real.log (100000000000 / 153807106599) ≤ (430529077 / 1000000000) := by
  have h := checkLog_sound (w := (53807106599 / 253807106599)) (n := 12)
    (lo := (107632269 / 250000000)) (hi := (430529077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((153807106599 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(153807106599 / 100000000000) = 1/(100000000000 / 153807106599) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7304 : Bounds (107632269 / 250000000) (430529077 / 1000000000) (Real.log (153807106599 / 100000000000)) := by
  have h := reflection_log_7304_neg
  have he : Real.log (153807106599 / 100000000000) = -Real.log (100000000000 / 153807106599) := by
    rw [show ((153807106599 / 100000000000) : ℝ) = ((100000000000 / 153807106599) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7305_neg : (192684343 / 1000000000) ≤ -Real.log (80 / 97) ∧
    -Real.log (80 / 97) ≤ (24085543 / 125000000) := by
  have h := checkLog_sound (w := (17 / 177)) (n := 12)
    (lo := (192684343 / 1000000000)) (hi := (24085543 / 125000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((97 / 80) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(97 / 80) = 1/(80 / 97) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7305 : Bounds (192684343 / 1000000000) (24085543 / 125000000) (Real.log (97 / 80)) := by
  have h := reflection_log_7305_neg
  have he : Real.log (97 / 80) = -Real.log (80 / 97) := by
    rw [show ((97 / 80) : ℝ) = ((80 / 97) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7306_neg : (59722977 / 250000000) ≤ -Real.log (63 / 80) ∧
    -Real.log (63 / 80) ≤ (238891909 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 143)) (n := 12)
    (lo := (59722977 / 250000000)) (hi := (238891909 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80 / 63) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80 / 63) = 1/(63 / 80) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7306 : Bounds (-238891909 / 1000000000) (-59722977 / 250000000) (Real.log (63 / 80)) := by
  have h := reflection_log_7306_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7307_neg : (212477 / 1000000000) ≤ -Real.log (80000 / 80017) ∧
    -Real.log (80000 / 80017) ≤ (106239 / 500000000) := by
  have h := checkLog_sound (w := (17 / 160017)) (n := 12)
    (lo := (212477 / 1000000000)) (hi := (106239 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80017 / 80000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80017 / 80000) = 1/(80000 / 80017) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7307 : Bounds (212477 / 1000000000) (106239 / 500000000) (Real.log (80017 / 80000)) := by
  have h := reflection_log_7307_neg
  have he : Real.log (80017 / 80000) = -Real.log (80000 / 80017) := by
    rw [show ((80017 / 80000) : ℝ) = ((80000 / 80017) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7308_neg : (106261 / 500000000) ≤ -Real.log (79983 / 80000) ∧
    -Real.log (79983 / 80000) ≤ (212523 / 1000000000) := by
  have h := checkLog_sound (w := (17 / 159983)) (n := 12)
    (lo := (106261 / 500000000)) (hi := (212523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((80000 / 79983) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(80000 / 79983) = 1/(79983 / 80000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7308 : Bounds (-212523 / 1000000000) (-106261 / 500000000) (Real.log (79983 / 80000)) := by
  have h := reflection_log_7308_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7309_neg : (20288269 / 200000000) ≤ -Real.log (200000 / 221353) ∧
    -Real.log (200000 / 221353) ≤ (50720673 / 500000000) := by
  have h := checkLog_sound (w := (21353 / 421353)) (n := 12)
    (lo := (20288269 / 200000000)) (hi := (50720673 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((221353 / 200000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(221353 / 200000) = 1/(200000 / 221353) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7309 : Bounds (20288269 / 200000000) (50720673 / 500000000) (Real.log (221353 / 200000)) := by
  have h := reflection_log_7309_neg
  have he : Real.log (221353 / 200000) = -Real.log (200000 / 221353) := by
    rw [show ((221353 / 200000) : ℝ) = ((200000 / 221353) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7310_neg : (56452787 / 500000000) ≤ -Real.log (178647 / 200000) ∧
    -Real.log (178647 / 200000) ≤ (4516223 / 40000000) := by
  have h := checkLog_sound (w := (21353 / 378647)) (n := 12)
    (lo := (56452787 / 500000000)) (hi := (4516223 / 40000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((200000 / 178647) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(200000 / 178647) = 1/(178647 / 200000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7310 : Bounds (-4516223 / 40000000) (-56452787 / 500000000) (Real.log (178647 / 200000)) := by
  have h := reflection_log_7310_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7311_neg : (10186411 / 100000000) ≤ -Real.log (1000000 / 1107233) ∧
    -Real.log (1000000 / 1107233) ≤ (101864111 / 1000000000) := by
  have h := checkLog_sound (w := (107233 / 2107233)) (n := 12)
    (lo := (10186411 / 100000000)) (hi := (101864111 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107233 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107233 / 1000000) = 1/(1000000 / 1107233) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7311 : Bounds (10186411 / 100000000) (101864111 / 1000000000) (Real.log (1107233 / 1000000)) := by
  have h := reflection_log_7311_neg
  have he : Real.log (1107233 / 1000000) = -Real.log (1000000 / 1107233) := by
    rw [show ((1107233 / 1000000) : ℝ) = ((1000000 / 1107233) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7312_neg : (2268593 / 20000000) ≤ -Real.log (892767 / 1000000) ∧
    -Real.log (892767 / 1000000) ≤ (113429651 / 1000000000) := by
  have h := checkLog_sound (w := (107233 / 1892767)) (n := 12)
    (lo := (2268593 / 20000000)) (hi := (113429651 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892767) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892767) = 1/(892767 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7312 : Bounds (-113429651 / 1000000000) (-2268593 / 20000000) (Real.log (892767 / 1000000)) := by
  have h := reflection_log_7312_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7313_neg : (578277 / 50000000) ≤ -Real.log (988501083711 / 1000000000000) ∧
    -Real.log (988501083711 / 1000000000000) ≤ (11565541 / 1000000000) := by
  have h := checkLog_sound (w := (11498916289 / 1988501083711)) (n := 12)
    (lo := (578277 / 50000000)) (hi := (11565541 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988501083711) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988501083711) = 1/(988501083711 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7313 : Bounds (-11565541 / 1000000000) (-578277 / 50000000) (Real.log (988501083711 / 1000000000000)) := by
  have h := reflection_log_7313_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7314_neg : (11464229 / 1000000000) ≤ -Real.log (39544049391 / 40000000000) ∧
    -Real.log (39544049391 / 40000000000) ≤ (1146423 / 100000000) := by
  have h := checkLog_sound (w := (455950609 / 79544049391)) (n := 12)
    (lo := (11464229 / 1000000000)) (hi := (1146423 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((40000000000 / 39544049391) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(40000000000 / 39544049391) = 1/(39544049391 / 40000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7314 : Bounds (-1146423 / 100000000) (-11464229 / 1000000000) (Real.log (39544049391 / 40000000000)) := by
  have h := reflection_log_7314_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7315_neg : (5358673 / 25000000) ≤ -Real.log (100000000000 / 123905243301) ∧
    -Real.log (100000000000 / 123905243301) ≤ (214346921 / 1000000000) := by
  have h := checkLog_sound (w := (23905243301 / 223905243301)) (n := 12)
    (lo := (5358673 / 25000000)) (hi := (214346921 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((123905243301 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(123905243301 / 100000000000) = 1/(100000000000 / 123905243301) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7315 : Bounds (5358673 / 25000000) (214346921 / 1000000000) (Real.log (123905243301 / 100000000000)) := by
  have h := reflection_log_7315_neg
  have he : Real.log (123905243301 / 100000000000) = -Real.log (100000000000 / 123905243301) := by
    rw [show ((123905243301 / 100000000000) : ℝ) = ((100000000000 / 123905243301) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7316_neg : (672793 / 3125000) ≤ -Real.log (250000000000 / 310056543309) ∧
    -Real.log (250000000000 / 310056543309) ≤ (215293761 / 1000000000) := by
  have h := checkLog_sound (w := (60056543309 / 560056543309)) (n := 12)
    (lo := (672793 / 3125000)) (hi := (215293761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310056543309 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310056543309 / 250000000000) = 1/(250000000000 / 310056543309) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7316 : Bounds (672793 / 3125000) (215293761 / 1000000000) (Real.log (310056543309 / 250000000000)) := by
  have h := reflection_log_7316_neg
  have he : Real.log (310056543309 / 250000000000) = -Real.log (250000000000 / 310056543309) := by
    rw [show ((310056543309 / 250000000000) : ℝ) = ((250000000000 / 310056543309) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7317_neg : (107632269 / 250000000) ≤ -Real.log (250000000000 / 384517766497) ∧
    -Real.log (250000000000 / 384517766497) ≤ (430529077 / 1000000000) := by
  have h := checkLog_sound (w := (134517766497 / 634517766497)) (n := 12)
    (lo := (107632269 / 250000000)) (hi := (430529077 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384517766497 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384517766497 / 250000000000) = 1/(250000000000 / 384517766497) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7317 : Bounds (107632269 / 250000000) (430529077 / 1000000000) (Real.log (384517766497 / 250000000000)) := by
  have h := reflection_log_7317_neg
  have he : Real.log (384517766497 / 250000000000) = -Real.log (250000000000 / 384517766497) := by
    rw [show ((384517766497 / 250000000000) : ℝ) = ((250000000000 / 384517766497) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7318_neg : (107894063 / 250000000) ≤ -Real.log (250000000000 / 384920634921) ∧
    -Real.log (250000000000 / 384920634921) ≤ (431576253 / 1000000000) := by
  have h := checkLog_sound (w := (134920634921 / 634920634921)) (n := 12)
    (lo := (107894063 / 250000000)) (hi := (431576253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((384920634921 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(384920634921 / 250000000000) = 1/(250000000000 / 384920634921) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7318 : Bounds (107894063 / 250000000) (431576253 / 1000000000) (Real.log (384920634921 / 250000000000)) := by
  have h := reflection_log_7318_neg
  have he : Real.log (384920634921 / 250000000000) = -Real.log (250000000000 / 384920634921) := by
    rw [show ((384920634921 / 250000000000) : ℝ) = ((250000000000 / 384920634921) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7319_neg : (193096629 / 1000000000) ≤ -Real.log (1000 / 1213) ∧
    -Real.log (1000 / 1213) ≤ (19309663 / 100000000) := by
  have h := checkLog_sound (w := (213 / 2213)) (n := 12)
    (lo := (193096629 / 1000000000)) (hi := (19309663 / 100000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1213 / 1000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1213 / 1000) = 1/(1000 / 1213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7319 : Bounds (193096629 / 1000000000) (19309663 / 100000000) (Real.log (1213 / 1000)) := by
  have h := reflection_log_7319_neg
  have he : Real.log (1213 / 1000) = -Real.log (1000 / 1213) := by
    rw [show ((1213 / 1000) : ℝ) = ((1000 / 1213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7320_neg : (23952703 / 100000000) ≤ -Real.log (787 / 1000) ∧
    -Real.log (787 / 1000) ≤ (239527031 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1787)) (n := 12)
    (lo := (23952703 / 100000000)) (hi := (239527031 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000 / 787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000 / 787) = 1/(787 / 1000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7320 : Bounds (-239527031 / 1000000000) (-23952703 / 100000000) (Real.log (787 / 1000)) := by
  have h := reflection_log_7320_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7321_neg : (212977 / 1000000000) ≤ -Real.log (1000000 / 1000213) ∧
    -Real.log (1000000 / 1000213) ≤ (106489 / 500000000) := by
  have h := checkLog_sound (w := (213 / 2000213)) (n := 12)
    (lo := (212977 / 1000000000)) (hi := (106489 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000213 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000213 / 1000000) = 1/(1000000 / 1000213) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7321 : Bounds (212977 / 1000000000) (106489 / 500000000) (Real.log (1000213 / 1000000)) := by
  have h := reflection_log_7321_neg
  have he : Real.log (1000213 / 1000000) = -Real.log (1000000 / 1000213) := by
    rw [show ((1000213 / 1000000) : ℝ) = ((1000000 / 1000213) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7322_neg : (106511 / 500000000) ≤ -Real.log (999787 / 1000000) ∧
    -Real.log (999787 / 1000000) ≤ (213023 / 1000000000) := by
  have h := checkLog_sound (w := (213 / 1999787)) (n := 12)
    (lo := (106511 / 500000000)) (hi := (213023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 999787) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 999787) = 1/(999787 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7322 : Bounds (-213023 / 1000000000) (-106511 / 500000000) (Real.log (999787 / 1000000)) := by
  have h := reflection_log_7322_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7323_neg : (101672623 / 1000000000) ≤ -Real.log (1000000 / 1107021) ∧
    -Real.log (1000000 / 1107021) ≤ (6354539 / 62500000) := by
  have h := checkLog_sound (w := (107021 / 2107021)) (n := 12)
    (lo := (101672623 / 1000000000)) (hi := (6354539 / 62500000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107021 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107021 / 1000000) = 1/(1000000 / 1107021) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7323 : Bounds (101672623 / 1000000000) (6354539 / 62500000) (Real.log (1107021 / 1000000)) := by
  have h := reflection_log_7323_neg
  have he : Real.log (1107021 / 1000000) = -Real.log (1000000 / 1107021) := by
    rw [show ((1107021 / 1000000) : ℝ) = ((1000000 / 1107021) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7324_neg : (56596107 / 500000000) ≤ -Real.log (892979 / 1000000) ∧
    -Real.log (892979 / 1000000) ≤ (22638443 / 200000000) := by
  have h := checkLog_sound (w := (107021 / 1892979)) (n := 12)
    (lo := (56596107 / 500000000)) (hi := (22638443 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892979) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892979) = 1/(892979 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7324 : Bounds (-22638443 / 200000000) (-56596107 / 500000000) (Real.log (892979 / 1000000)) := by
  have h := reflection_log_7324_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7325_neg : (10209529 / 100000000) ≤ -Real.log (1000000 / 1107489) ∧
    -Real.log (1000000 / 1107489) ≤ (102095291 / 1000000000) := by
  have h := checkLog_sound (w := (107489 / 2107489)) (n := 12)
    (lo := (10209529 / 100000000)) (hi := (102095291 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107489 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107489 / 1000000) = 1/(1000000 / 1107489) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7325 : Bounds (10209529 / 100000000) (102095291 / 1000000000) (Real.log (1107489 / 1000000)) := by
  have h := reflection_log_7325_neg
  have he : Real.log (1107489 / 1000000) = -Real.log (1000000 / 1107489) := by
    rw [show ((1107489 / 1000000) : ℝ) = ((1000000 / 1107489) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7326_neg : (2842911 / 25000000) ≤ -Real.log (892511 / 1000000) ∧
    -Real.log (892511 / 1000000) ≤ (113716441 / 1000000000) := by
  have h := checkLog_sound (w := (107489 / 1892511)) (n := 12)
    (lo := (2842911 / 25000000)) (hi := (113716441 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892511) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892511) = 1/(892511 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7326 : Bounds (-113716441 / 1000000000) (-2842911 / 25000000) (Real.log (892511 / 1000000)) := by
  have h := reflection_log_7326_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7327_neg : (11621149 / 1000000000) ≤ -Real.log (988446114879 / 1000000000000) ∧
    -Real.log (988446114879 / 1000000000000) ≤ (232423 / 20000000) := by
  have h := checkLog_sound (w := (11553885121 / 1988446114879)) (n := 12)
    (lo := (11621149 / 1000000000)) (hi := (232423 / 20000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988446114879) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988446114879) = 1/(988446114879 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7327 : Bounds (-232423 / 20000000) (-11621149 / 1000000000) (Real.log (988446114879 / 1000000000000)) := by
  have h := reflection_log_7327_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7328_neg : (1151959 / 100000000) ≤ -Real.log (988546505559 / 1000000000000) ∧
    -Real.log (988546505559 / 1000000000000) ≤ (11519591 / 1000000000) := by
  have h := checkLog_sound (w := (11453494441 / 1988546505559)) (n := 12)
    (lo := (1151959 / 100000000)) (hi := (11519591 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988546505559) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988546505559) = 1/(988546505559 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7328 : Bounds (-11519591 / 1000000000) (-1151959 / 100000000) (Real.log (988546505559 / 1000000000000)) := by
  have h := reflection_log_7328_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7329_neg : (107432419 / 500000000) ≤ -Real.log (500000000000 / 619847163259) ∧
    -Real.log (500000000000 / 619847163259) ≤ (214864839 / 1000000000) := by
  have h := checkLog_sound (w := (119847163259 / 1119847163259)) (n := 12)
    (lo := (107432419 / 500000000)) (hi := (214864839 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((619847163259 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(619847163259 / 500000000000) = 1/(500000000000 / 619847163259) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7329 : Bounds (107432419 / 500000000) (214864839 / 1000000000) (Real.log (619847163259 / 500000000000)) := by
  have h := reflection_log_7329_neg
  have he : Real.log (619847163259 / 500000000000) = -Real.log (500000000000 / 619847163259) := by
    rw [show ((619847163259 / 500000000000) : ℝ) = ((500000000000 / 619847163259) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7330_neg : (215811731 / 1000000000) ≤ -Real.log (500000000000 / 620434369997) ∧
    -Real.log (500000000000 / 620434369997) ≤ (53952933 / 250000000) := by
  have h := checkLog_sound (w := (120434369997 / 1120434369997)) (n := 12)
    (lo := (215811731 / 1000000000)) (hi := (53952933 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620434369997 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620434369997 / 500000000000) = 1/(500000000000 / 620434369997) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7330 : Bounds (215811731 / 1000000000) (53952933 / 250000000) (Real.log (620434369997 / 500000000000)) := by
  have h := reflection_log_7330_neg
  have he : Real.log (620434369997 / 500000000000) = -Real.log (500000000000 / 620434369997) := by
    rw [show ((620434369997 / 500000000000) : ℝ) = ((500000000000 / 620434369997) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7331_neg : (107894063 / 250000000) ≤ -Real.log (500000000000 / 769841269841) ∧
    -Real.log (500000000000 / 769841269841) ≤ (431576253 / 1000000000) := by
  have h := checkLog_sound (w := (269841269841 / 1269841269841)) (n := 12)
    (lo := (107894063 / 250000000)) (hi := (431576253 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((769841269841 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(769841269841 / 500000000000) = 1/(500000000000 / 769841269841) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7331 : Bounds (107894063 / 250000000) (431576253 / 1000000000) (Real.log (769841269841 / 500000000000)) := by
  have h := reflection_log_7331_neg
  have he : Real.log (769841269841 / 500000000000) = -Real.log (500000000000 / 769841269841) := by
    rw [show ((769841269841 / 500000000000) : ℝ) = ((500000000000 / 769841269841) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7332_neg : (21631183 / 50000000) ≤ -Real.log (15625000000 / 24082750953) ∧
    -Real.log (15625000000 / 24082750953) ≤ (432623661 / 1000000000) := by
  have h := checkLog_sound (w := (8457750953 / 39707750953)) (n := 12)
    (lo := (21631183 / 50000000)) (hi := (432623661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((24082750953 / 15625000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(24082750953 / 15625000000) = 1/(15625000000 / 24082750953) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7332 : Bounds (21631183 / 50000000) (432623661 / 1000000000) (Real.log (24082750953 / 15625000000)) := by
  have h := reflection_log_7332_neg
  have he : Real.log (24082750953 / 15625000000) = -Real.log (15625000000 / 24082750953) := by
    rw [show ((24082750953 / 15625000000) : ℝ) = ((15625000000 / 24082750953) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7333_neg : (96754373 / 500000000) ≤ -Real.log (2000 / 2427) ∧
    -Real.log (2000 / 2427) ≤ (193508747 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 4427)) (n := 12)
    (lo := (96754373 / 500000000)) (hi := (193508747 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2427 / 2000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2427 / 2000) = 1/(2000 / 2427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7333 : Bounds (96754373 / 500000000) (193508747 / 1000000000) (Real.log (2427 / 2000)) := by
  have h := reflection_log_7333_neg
  have he : Real.log (2427 / 2000) = -Real.log (2000 / 2427) := by
    rw [show ((2427 / 2000) : ℝ) = ((2000 / 2427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7334_neg : (60040639 / 250000000) ≤ -Real.log (1573 / 2000) ∧
    -Real.log (1573 / 2000) ≤ (240162557 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 3573)) (n := 12)
    (lo := (60040639 / 250000000)) (hi := (240162557 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000 / 1573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000 / 1573) = 1/(1573 / 2000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7334 : Bounds (-240162557 / 1000000000) (-60040639 / 250000000) (Real.log (1573 / 2000)) := by
  have h := reflection_log_7334_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7335_neg : (213477 / 1000000000) ≤ -Real.log (2000000 / 2000427) ∧
    -Real.log (2000000 / 2000427) ≤ (106739 / 500000000) := by
  have h := checkLog_sound (w := (427 / 4000427)) (n := 12)
    (lo := (213477 / 1000000000)) (hi := (106739 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000427 / 2000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000427 / 2000000) = 1/(2000000 / 2000427) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7335 : Bounds (213477 / 1000000000) (106739 / 500000000) (Real.log (2000427 / 2000000)) := by
  have h := reflection_log_7335_neg
  have he : Real.log (2000427 / 2000000) = -Real.log (2000000 / 2000427) := by
    rw [show ((2000427 / 2000000) : ℝ) = ((2000000 / 2000427) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7336_neg : (106761 / 500000000) ≤ -Real.log (1999573 / 2000000) ∧
    -Real.log (1999573 / 2000000) ≤ (213523 / 1000000000) := by
  have h := checkLog_sound (w := (427 / 3999573)) (n := 12)
    (lo := (106761 / 500000000)) (hi := (213523 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((2000000 / 1999573) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(2000000 / 1999573) = 1/(1999573 / 2000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7336 : Bounds (-213523 / 1000000000) (-106761 / 500000000) (Real.log (1999573 / 2000000)) := by
  have h := reflection_log_7336_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7337_neg : (12737981 / 125000000) ≤ -Real.log (1000000 / 1107277) ∧
    -Real.log (1000000 / 1107277) ≤ (101903849 / 1000000000) := by
  have h := checkLog_sound (w := (107277 / 2107277)) (n := 12)
    (lo := (12737981 / 125000000)) (hi := (101903849 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107277 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107277 / 1000000) = 1/(1000000 / 1107277) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7337 : Bounds (12737981 / 125000000) (101903849 / 1000000000) (Real.log (1107277 / 1000000)) := by
  have h := reflection_log_7337_neg
  have he : Real.log (1107277 / 1000000) = -Real.log (1000000 / 1107277) := by
    rw [show ((1107277 / 1000000) : ℝ) = ((1000000 / 1107277) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7338_neg : (14184867 / 125000000) ≤ -Real.log (892723 / 1000000) ∧
    -Real.log (892723 / 1000000) ≤ (113478937 / 1000000000) := by
  have h := checkLog_sound (w := (107277 / 1892723)) (n := 12)
    (lo := (14184867 / 125000000)) (hi := (113478937 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892723) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892723) = 1/(892723 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7338 : Bounds (-113478937 / 1000000000) (-14184867 / 125000000) (Real.log (892723 / 1000000)) := by
  have h := reflection_log_7338_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7339_neg : (2558183 / 25000000) ≤ -Real.log (500000 / 553873) ∧
    -Real.log (500000 / 553873) ≤ (102327321 / 1000000000) := by
  have h := checkLog_sound (w := (53873 / 1053873)) (n := 12)
    (lo := (2558183 / 25000000)) (hi := (102327321 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((553873 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(553873 / 500000) = 1/(500000 / 553873) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7339 : Bounds (2558183 / 25000000) (102327321 / 1000000000) (Real.log (553873 / 500000)) := by
  have h := reflection_log_7339_neg
  have he : Real.log (553873 / 500000) = -Real.log (500000 / 553873) := by
    rw [show ((553873 / 500000) : ℝ) = ((500000 / 553873) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7340_neg : (114004433 / 1000000000) ≤ -Real.log (446127 / 500000) ∧
    -Real.log (446127 / 500000) ≤ (57002217 / 500000000) := by
  have h := checkLog_sound (w := (53873 / 946127)) (n := 12)
    (lo := (114004433 / 1000000000)) (hi := (57002217 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 446127) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 446127) = 1/(446127 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7340 : Bounds (-57002217 / 500000000) (-114004433 / 1000000000) (Real.log (446127 / 500000)) := by
  have h := reflection_log_7340_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7341_neg : (11677113 / 1000000000) ≤ -Real.log (247097699871 / 250000000000) ∧
    -Real.log (247097699871 / 250000000000) ≤ (5838557 / 500000000) := by
  have h := checkLog_sound (w := (2902300129 / 497097699871)) (n := 12)
    (lo := (11677113 / 1000000000)) (hi := (5838557 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247097699871) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247097699871) = 1/(247097699871 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7341 : Bounds (-5838557 / 500000000) (-11677113 / 1000000000) (Real.log (247097699871 / 250000000000)) := by
  have h := reflection_log_7341_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7342_neg : (723443 / 62500000) ≤ -Real.log (988491645271 / 1000000000000) ∧
    -Real.log (988491645271 / 1000000000000) ≤ (11575089 / 1000000000) := by
  have h := checkLog_sound (w := (11508354729 / 1988491645271)) (n := 12)
    (lo := (723443 / 62500000)) (hi := (11575089 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988491645271) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988491645271) = 1/(988491645271 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7342 : Bounds (-11575089 / 1000000000) (-723443 / 62500000) (Real.log (988491645271 / 1000000000000)) := by
  have h := reflection_log_7342_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7343_neg : (841339 / 3906250) ≤ -Real.log (125000000000 / 155042073521) ∧
    -Real.log (125000000000 / 155042073521) ≤ (43076557 / 200000000) := by
  have h := checkLog_sound (w := (30042073521 / 280042073521)) (n := 12)
    (lo := (841339 / 3906250)) (hi := (43076557 / 200000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((155042073521 / 125000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(155042073521 / 125000000000) = 1/(125000000000 / 155042073521) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7343 : Bounds (841339 / 3906250) (43076557 / 200000000) (Real.log (155042073521 / 125000000000)) := by
  have h := reflection_log_7343_neg
  have he : Real.log (155042073521 / 125000000000) = -Real.log (125000000000 / 155042073521) := by
    rw [show ((155042073521 / 125000000000) : ℝ) = ((125000000000 / 155042073521) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7344_neg : (216331753 / 1000000000) ≤ -Real.log (500000000000 / 620757093833) ∧
    -Real.log (500000000000 / 620757093833) ≤ (108165877 / 500000000) := by
  have h := checkLog_sound (w := (120757093833 / 1120757093833)) (n := 12)
    (lo := (216331753 / 1000000000)) (hi := (108165877 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620757093833 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620757093833 / 500000000000) = 1/(500000000000 / 620757093833) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7344 : Bounds (216331753 / 1000000000) (108165877 / 500000000) (Real.log (620757093833 / 500000000000)) := by
  have h := reflection_log_7344_neg
  have he : Real.log (620757093833 / 500000000000) = -Real.log (500000000000 / 620757093833) := by
    rw [show ((620757093833 / 500000000000) : ℝ) = ((500000000000 / 620757093833) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7345_neg : (21631183 / 50000000) ≤ -Real.log (100000000000 / 154129606099) ∧
    -Real.log (100000000000 / 154129606099) ≤ (432623661 / 1000000000) := by
  have h := checkLog_sound (w := (54129606099 / 254129606099)) (n := 12)
    (lo := (21631183 / 50000000)) (hi := (432623661 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((154129606099 / 100000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(154129606099 / 100000000000) = 1/(100000000000 / 154129606099) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7345 : Bounds (21631183 / 50000000) (432623661 / 1000000000) (Real.log (154129606099 / 100000000000)) := by
  have h := reflection_log_7345_neg
  have he : Real.log (154129606099 / 100000000000) = -Real.log (100000000000 / 154129606099) := by
    rw [show ((154129606099 / 100000000000) : ℝ) = ((100000000000 / 154129606099) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7346_neg : (216835651 / 500000000) ≤ -Real.log (500000000000 / 771455816911) ∧
    -Real.log (500000000000 / 771455816911) ≤ (433671303 / 1000000000) := by
  have h := checkLog_sound (w := (271455816911 / 1271455816911)) (n := 12)
    (lo := (216835651 / 500000000)) (hi := (433671303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((771455816911 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(771455816911 / 500000000000) = 1/(500000000000 / 771455816911) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7346 : Bounds (216835651 / 500000000) (433671303 / 1000000000) (Real.log (771455816911 / 500000000000)) := by
  have h := reflection_log_7346_neg
  have he : Real.log (771455816911 / 500000000000) = -Real.log (500000000000 / 771455816911) := by
    rw [show ((771455816911 / 500000000000) : ℝ) = ((500000000000 / 771455816911) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7347_neg : (48480173 / 250000000) ≤ -Real.log (500 / 607) ∧
    -Real.log (500 / 607) ≤ (193920693 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 1107)) (n := 12)
    (lo := (48480173 / 250000000)) (hi := (193920693 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((607 / 500) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(607 / 500) = 1/(500 / 607) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7347 : Bounds (48480173 / 250000000) (193920693 / 1000000000) (Real.log (607 / 500)) := by
  have h := reflection_log_7347_neg
  have he : Real.log (607 / 500) = -Real.log (500 / 607) := by
    rw [show ((607 / 500) : ℝ) = ((500 / 607) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7348_neg : (120399243 / 500000000) ≤ -Real.log (393 / 500) ∧
    -Real.log (393 / 500) ≤ (240798487 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 893)) (n := 12)
    (lo := (120399243 / 500000000)) (hi := (240798487 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500 / 393) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500 / 393) = 1/(393 / 500) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7348 : Bounds (-240798487 / 1000000000) (-120399243 / 500000000) (Real.log (393 / 500)) := by
  have h := reflection_log_7348_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7349_neg : (213977 / 1000000000) ≤ -Real.log (500000 / 500107) ∧
    -Real.log (500000 / 500107) ≤ (106989 / 500000000) := by
  have h := checkLog_sound (w := (107 / 1000107)) (n := 12)
    (lo := (213977 / 1000000000)) (hi := (106989 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500107 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500107 / 500000) = 1/(500000 / 500107) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7349 : Bounds (213977 / 1000000000) (106989 / 500000000) (Real.log (500107 / 500000)) := by
  have h := reflection_log_7349_neg
  have he : Real.log (500107 / 500000) = -Real.log (500000 / 500107) := by
    rw [show ((500107 / 500000) : ℝ) = ((500000 / 500107) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7350_neg : (107011 / 500000000) ≤ -Real.log (499893 / 500000) ∧
    -Real.log (499893 / 500000) ≤ (214023 / 1000000000) := by
  have h := checkLog_sound (w := (107 / 999893)) (n := 12)
    (lo := (107011 / 500000000)) (hi := (214023 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 499893) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 499893) = 1/(499893 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7350 : Bounds (-214023 / 1000000000) (-107011 / 500000000) (Real.log (499893 / 500000)) := by
  have h := reflection_log_7350_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7351_neg : (102135019 / 1000000000) ≤ -Real.log (1000000 / 1107533) ∧
    -Real.log (1000000 / 1107533) ≤ (5106751 / 50000000) := by
  have h := checkLog_sound (w := (107533 / 2107533)) (n := 12)
    (lo := (102135019 / 1000000000)) (hi := (5106751 / 50000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1107533 / 1000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1107533 / 1000000) = 1/(1000000 / 1107533) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7351 : Bounds (102135019 / 1000000000) (5106751 / 50000000) (Real.log (1107533 / 1000000)) := by
  have h := reflection_log_7351_neg
  have he : Real.log (1107533 / 1000000) = -Real.log (1000000 / 1107533) := by
    rw [show ((1107533 / 1000000) : ℝ) = ((1000000 / 1107533) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7352_neg : (5688287 / 50000000) ≤ -Real.log (892467 / 1000000) ∧
    -Real.log (892467 / 1000000) ≤ (113765741 / 1000000000) := by
  have h := checkLog_sound (w := (107533 / 1892467)) (n := 12)
    (lo := (5688287 / 50000000)) (hi := (113765741 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000 / 892467) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000 / 892467) = 1/(892467 / 1000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7352 : Bounds (-113765741 / 1000000000) (-5688287 / 50000000) (Real.log (892467 / 1000000)) := by
  have h := reflection_log_7352_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7353_neg : (102558393 / 1000000000) ≤ -Real.log (500000 / 554001) ∧
    -Real.log (500000 / 554001) ≤ (51279197 / 500000000) := by
  have h := checkLog_sound (w := (54001 / 1054001)) (n := 12)
    (lo := (102558393 / 1000000000)) (hi := (51279197 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((554001 / 500000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(554001 / 500000) = 1/(500000 / 554001) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7353 : Bounds (102558393 / 1000000000) (51279197 / 500000000) (Real.log (554001 / 500000)) := by
  have h := reflection_log_7353_neg
  have he : Real.log (554001 / 500000) = -Real.log (500000 / 554001) := by
    rw [show ((554001 / 500000) : ℝ) = ((500000 / 554001) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7354_neg : (28572847 / 250000000) ≤ -Real.log (445999 / 500000) ∧
    -Real.log (445999 / 500000) ≤ (114291389 / 1000000000) := by
  have h := checkLog_sound (w := (54001 / 945999)) (n := 12)
    (lo := (28572847 / 250000000)) (hi := (114291389 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((500000 / 445999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(500000 / 445999) = 1/(445999 / 500000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7354 : Bounds (-114291389 / 1000000000) (-28572847 / 250000000) (Real.log (445999 / 500000)) := by
  have h := reflection_log_7354_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7355_neg : (2346599 / 200000000) ≤ -Real.log (247083891999 / 250000000000) ∧
    -Real.log (247083891999 / 250000000000) ≤ (2933249 / 250000000) := by
  have h := checkLog_sound (w := (2916108001 / 497083891999)) (n := 12)
    (lo := (2346599 / 200000000)) (hi := (2933249 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((250000000000 / 247083891999) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(250000000000 / 247083891999) = 1/(247083891999 / 250000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7355 : Bounds (-2933249 / 250000000) (-2346599 / 200000000) (Real.log (247083891999 / 250000000000)) := by
  have h := reflection_log_7355_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7356_neg : (11630721 / 1000000000) ≤ -Real.log (988436653911 / 1000000000000) ∧
    -Real.log (988436653911 / 1000000000000) ≤ (5815361 / 500000000) := by
  have h := checkLog_sound (w := (11563346089 / 1988436653911)) (n := 12)
    (lo := (11630721 / 1000000000)) (hi := (5815361 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((1000000000000 / 988436653911) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(1000000000000 / 988436653911) = 1/(988436653911 / 1000000000000) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7356 : Bounds (-5815361 / 500000000) (-11630721 / 1000000000) (Real.log (988436653911 / 1000000000000)) := by
  have h := reflection_log_7356_neg
  constructor <;> linarith [h.1,h.2]

theorem reflection_log_7357_neg : (5397519 / 25000000) ≤ -Real.log (500000000000 / 620489609139) ∧
    -Real.log (500000000000 / 620489609139) ≤ (215900761 / 1000000000) := by
  have h := checkLog_sound (w := (120489609139 / 1120489609139)) (n := 12)
    (lo := (5397519 / 25000000)) (hi := (215900761 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((620489609139 / 500000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(620489609139 / 500000000000) = 1/(500000000000 / 620489609139) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7357 : Bounds (5397519 / 25000000) (215900761 / 1000000000) (Real.log (620489609139 / 500000000000)) := by
  have h := reflection_log_7357_neg
  have he : Real.log (620489609139 / 500000000000) = -Real.log (500000000000 / 620489609139) := by
    rw [show ((620489609139 / 500000000000) : ℝ) = ((500000000000 / 620489609139) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7358_neg : (216849781 / 1000000000) ≤ -Real.log (250000000000 / 310539373407) ∧
    -Real.log (250000000000 / 310539373407) ≤ (108424891 / 500000000) := by
  have h := checkLog_sound (w := (60539373407 / 560539373407)) (n := 12)
    (lo := (216849781 / 1000000000)) (hi := (108424891 / 500000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((310539373407 / 250000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(310539373407 / 250000000000) = 1/(250000000000 / 310539373407) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7358 : Bounds (216849781 / 1000000000) (108424891 / 500000000) (Real.log (310539373407 / 250000000000)) := by
  have h := reflection_log_7358_neg
  have he : Real.log (310539373407 / 250000000000) = -Real.log (250000000000 / 310539373407) := by
    rw [show ((310539373407 / 250000000000) : ℝ) = ((250000000000 / 310539373407) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

theorem reflection_log_7359_neg : (216835651 / 500000000) ≤ -Real.log (50000000000 / 77145581691) ∧
    -Real.log (50000000000 / 77145581691) ≤ (433671303 / 1000000000) := by
  have h := checkLog_sound (w := (27145581691 / 127145581691)) (n := 12)
    (lo := (216835651 / 500000000)) (hi := (433671303 / 1000000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((77145581691 / 50000000000) : ℝ) 0 (by norm_num)
  have hq : (2 : ℝ)^0*(77145581691 / 50000000000) = 1/(50000000000 / 77145581691) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]


theorem reflection_log_7359 : Bounds (216835651 / 500000000) (433671303 / 1000000000) (Real.log (77145581691 / 50000000000)) := by
  have h := reflection_log_7359_neg
  have he : Real.log (77145581691 / 50000000000) = -Real.log (50000000000 / 77145581691) := by
    rw [show ((77145581691 / 50000000000) : ℝ) = ((50000000000 / 77145581691) : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [he]
  exact h

end GeneralCK.Certificates.LowRatioFamily

end


