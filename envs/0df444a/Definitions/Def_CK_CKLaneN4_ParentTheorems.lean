-- Prove2me | Definitions.Def_CK_CKLaneN4_ParentTheorems
-- name    : CK_CKLaneN4_ParentTheorems
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-01T10:24:58.763985+00:00
-- url     : https://prove2.me/theorems/75da9b13-f7c4-4afa-86df-0a05e6b2ec0d
-- title:
--   Courtade–Kumar proof module `CKLaneN4.ParentTheorems` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN4.ParentTheorems` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN4.ParentTheorems` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN4.ParentTheorems (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN4/ParentTheorems.lean)

import Definitions.Def_CK_CKLaneN4_ParentTheorems_q02

namespace CKLaneN4
open GeneralCK
/-- Mean form of PARENT8 (any parent mean `m`, bias `|1 - 2m|`). -/
theorem parent8_mean {m E : ℝ} (hE : 0 < E) (hq : 0 < |1 - 2 * m|) (hq25 : |1 - 2 * m| ≤ 2 / 5)
    (h8 : 8 * E ≤ |1 - 2 * m|) : psi m E < phi m E := by
  have h := parent8 _ E hE hq hq25 h8
  rcases le_total 0 (1 - 2 * m) with hs | hs
  · rw [abs_of_nonneg hs] at h
    simpa only [show (1 - (1 - 2 * m)) / 2 = m by ring] using h
  · rw [abs_of_nonpos hs] at h
    have e : (1 - -(1 - 2 * m)) / 2 = 1 - m := by ring
    rw [e] at h
    unfold phi psi at h ⊢
    rwa [H_complement, show |1 - 2 * (1 - m)| = |1 - 2 * m| by
      rw [show 1 - 2 * (1 - m) = -(1 - 2 * m) by ring, abs_neg]] at h

end CKLaneN4


