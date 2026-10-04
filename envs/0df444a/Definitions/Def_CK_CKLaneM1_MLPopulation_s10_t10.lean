-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_s10_t10
-- name    : CK_CKLaneM1_MLPopulation_s10_t10
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:54:39.324529+00:00
-- url     : https://prove2.me/theorems/3ec8161f-427a-44a6-b4a2-d5dcdaee1fca
-- title:
--   Courtade–Kumar proof module `CKLaneM1.ML.Population (supergroup 10 tree 10)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.ML.Population (supergroup 10 tree 10)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.ML.Population (supergroup 10 tree 10)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.ML.Population (supergroup 10 tree 10) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/ML/Population (supergroup 10 tree 10).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation_h084
import Definitions.Def_CK_CKLaneM1_MLPopulation_h085

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def sgt_10_10 : List (List ℕ × LeafCert) :=
  leafgrp_084 ++ leafgrp_085

theorem sgt_10_10_sem : ∀ x ∈ sgt_10_10, SemSS (ssBox x.1) :=
  sem_append leafgrp_084_sem leafgrp_085_sem

end CKLaneM1.ML.Population


