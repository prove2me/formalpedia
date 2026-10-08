-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_s01_t1
-- name    : CK_CKLaneM1_MLPopulation_s01_t1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T11:58:39.912614+00:00
-- url     : https://prove2.me/theorems/f6cef3de-e341-4901-81e5-2db2a1dc0608
-- title:
--   Courtade–Kumar proof module `CKLaneM1.ML.Population (supergroup 01 tree 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.ML.Population (supergroup 01 tree 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.ML.Population (supergroup 01 tree 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.ML.Population (supergroup 01 tree 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/ML/Population (supergroup 01 tree 1).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation_s01_t10
import Definitions.Def_CK_CKLaneM1_MLPopulation_s01_t11

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def sgt_01_1 : List (List ℕ × LeafCert) :=
  sgt_01_10 ++ sgt_01_11

theorem sgt_01_1_sem : ∀ x ∈ sgt_01_1, SemSS (ssBox x.1) :=
  sem_append sgt_01_10_sem sgt_01_11_sem

end CKLaneM1.ML.Population


