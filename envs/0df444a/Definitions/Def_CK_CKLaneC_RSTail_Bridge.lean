-- Prove2me | Definitions.Def_CK_CKLaneC_RSTail_Bridge
-- name    : CK_CKLaneC_RSTail_Bridge
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-30T05:00:27.65576+00:00
-- url     : https://prove2.me/theorems/db83ab48-edac-4a3f-b9c5-bf24cb9fb1db
-- title:
--   Courtade–Kumar proof module `CKLaneC.RSTail.Bridge` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneC.RSTail.Bridge` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneC.RSTail.Bridge` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneC.RSTail.Bridge (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneC/RSTail/Bridge.lean)

import Definitions.Def_CK_CKLaneC_RSTail_Region
import Definitions.Def_CK_CKLaneR2_Cell_Defs

-- ===== source module CKLaneC.RSTail.Bridge =====
section

/-! Lane C: bridge from R2b's leaf conclusions (stated with `CKLaneR2.Cell.one`) to `TailPosI` (`CKLaneC.RSCell.one`). -/

namespace CKLaneC.RSTail

theorem ofR2 {b0 b1 t0 t1 s0 s1 : Int}
    (h : ∀ b t σ : ℝ, (b0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ b → b ≤ (b1 : ℝ) / (CKLaneR2.Cell.one : ℝ) →
      (t0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ t → t ≤ (t1 : ℝ) / (CKLaneR2.Cell.one : ℝ) →
      (s0 : ℝ) / (CKLaneR2.Cell.one : ℝ) ≤ σ → σ ≤ (s1 : ℝ) / (CKLaneR2.Cell.one : ℝ) → 0 < σ →
      0 < CKLaneN23.RS.rayGamma b t (b - b * σ)) :
    TailPosI b0 b1 t0 t1 s0 s1 := h

end CKLaneC.RSTail

end


