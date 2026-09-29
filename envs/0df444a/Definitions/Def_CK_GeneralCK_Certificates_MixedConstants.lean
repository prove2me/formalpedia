-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_MixedConstants
-- name    : CK_GeneralCK_Certificates_MixedConstants
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:22:30.938615+00:00
-- url     : https://prove2.me/theorems/3a2d820a-fa1e-43c6-ab42-7c1de6f8edbb
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.MixedConstants` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.MixedConstants` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.MixedConstants` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.MixedConstants (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedConstants.lean)

import Definitions.Def_CK_GeneralCK_Certificates_MixedBounds

namespace GeneralCK.Certificates.Mixed

theorem log_inv_twenty_one : (608904487 / 200000000) ≤ -Real.log (1 / 21) ∧
    -Real.log (1 / 21) ≤ (76113061 / 25000000) := by
  have h := checkLog_sound (w := (5 / 37)) (n := 12)
    (lo := (54386743 / 200000000)) (hi := (67983429 / 250000000))
    (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h
  have hs := log_scaled ((21 / 16) : ℝ) 4 (by norm_num)
  have hq : (2 : ℝ)^4*(21 / 16) = 1/(1 / 21) := by norm_num
  rw [hq, log_inv_eq] at hs
  have htwo := PilotData.log_two
  norm_num at hs htwo ⊢
  constructor <;> linarith only [h.1, h.2, htwo.1, htwo.2, hs]

theorem log_twenty_one_gt_three : (3 : ℝ) < Real.log 21 := by
  have h := log_inv_twenty_one
  rw [one_div, Real.log_inv, neg_neg] at h
  linarith only [h.1]

theorem log_two_gt_69 : (69/100 : ℝ) < Real.log 2 := by
  have h := PilotData.log_two
  norm_num at h
  linarith only [h.1]

end GeneralCK.Certificates.Mixed


