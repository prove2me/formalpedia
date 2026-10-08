-- Prove2me | Definitions.Def_CK_CKLaneM07_CE_R3Oct_K9
-- name    : CK_CKLaneM07_CE_R3Oct_K9
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-06T11:13:22.227351+00:00
-- url     : https://prove2.me/theorems/b70ae631-0b82-4213-ad35-ad5b66ca67ce
-- title:
--   Courtade–Kumar proof module `CKLaneM07.CE.R3Oct.K9` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM07.CE.R3Oct.K9` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM07.CE.R3Oct.K9` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM07.CE.R3Oct.K9 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM07/CE/R3Oct/K9.lean)

import Definitions.Def_CK_CKLaneM07_CE_R3Roots
import Definitions.Def_CK_CKLaneM07_CE_R3Glue
import Definitions.Def_CK_CKLaneM07_CE_R3Cells_K9_S0000

-- ===== source module CKLaneM07.CE.R3Oct.K9 =====
section

/-! Lane M07 row-3 octave k=9: 1 shards glued along the generated skeleton (R3Glue). -/

namespace CKLaneM07.CE.R3Oct.K9

open CKLaneN1 CKLaneM07.CE.R3Roots CKLaneM07.CE.R3Glue

set_option maxRecDepth 100000 in
theorem sem : CKLaneN1.R3.Sem root9 :=
  sem_eq (by decide +kernel) CKLaneM07.CE.R3Cells.K9.S0000.sem

end CKLaneM07.CE.R3Oct.K9

end


