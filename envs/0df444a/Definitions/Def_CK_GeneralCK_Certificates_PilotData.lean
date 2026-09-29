-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_PilotData
-- name    : CK_GeneralCK_Certificates_PilotData
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-27T22:17:23.679606+00:00
-- url     : https://prove2.me/theorems/170bc6d3-2b67-4cd1-a6d1-86ed6a91d363
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.PilotData` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.PilotData` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.PilotData` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.PilotData (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/PilotData.lean)

import Definitions.Def_CK_GeneralCK_Certificates_LogBounds

/-! Generated rational witnesses for the retained diagonal contact pilot. -/
namespace GeneralCK.Certificates.PilotData

theorem log_two :
    (34657359 / 50000000) ≤ Real.log (2 / 1) ∧
    Real.log (2 / 1) ≤ (693147181 / 1000000000) := by
  have h := checkLog_sound (w := (1 / 3)) (n := 12)
    (lo := (34657359 / 50000000)) (hi := (693147181 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_left :
    (262151201 / 500000000) ≤ Real.log (5279 / 3125) ∧
    Real.log (5279 / 3125) ≤ (524302403 / 1000000000) := by
  have h := checkLog_sound (w := (1077 / 4202)) (n := 12)
    (lo := (262151201 / 500000000)) (hi := (524302403 / 1000000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_scaled_right :
    (262245907 / 500000000) ≤ Real.log (1056 / 625) ∧
    Real.log (1056 / 625) ≤ (104898363 / 200000000) := by
  have h := checkLog_sound (w := (431 / 1681)) (n := 12)
    (lo := (262245907 / 500000000)) (hi := (104898363 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_left :
    (54234457 / 1000000000) ≤ Real.log (100000 / 94721) ∧
    Real.log (100000 / 94721) ≤ (27117229 / 500000000) := by
  have h := checkLog_sound (w := (5279 / 194721)) (n := 12)
    (lo := (54234457 / 1000000000)) (hi := (27117229 / 500000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

theorem log_inv_complement_right :
    (27122507 / 500000000) ≤ Real.log (625 / 592) ∧
    Real.log (625 / 592) ≤ (10849003 / 200000000) := by
  have h := checkLog_sound (w := (33 / 1217)) (n := 12)
    (lo := (27122507 / 500000000)) (hi := (10849003 / 200000000)) (by norm_num [checkLog, logLower, logUpper, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

end GeneralCK.Certificates.PilotData


