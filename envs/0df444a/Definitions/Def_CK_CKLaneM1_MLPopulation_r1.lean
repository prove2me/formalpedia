-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_r1
-- name    : CK_CKLaneM1_MLPopulation_r1
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T21:35:41.192141+00:00
-- url     : https://prove2.me/theorems/a1a01535-30ad-496a-8e1d-c96a1c48de1c
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulation (supergroup combine node 1)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulation (supergroup combine node 1)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulation (supergroup combine node 1)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulation (supergroup combine node 1) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulation (supergroup combine node 1).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation_r10
import Definitions.Def_CK_CKLaneM1_MLPopulation_r11

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def allgrp_1 : List (List ℕ × LeafCert) :=
  allgrp_10 ++ allgrp_11

theorem allgrp_1_sem : ∀ x ∈ allgrp_1, SemSS (ssBox x.1) :=
  sem_append allgrp_10_sem allgrp_11_sem

end CKLaneM1.ML.Population


