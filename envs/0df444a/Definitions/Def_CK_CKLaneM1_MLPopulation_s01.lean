-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_s01
-- name    : CK_CKLaneM1_MLPopulation_s01
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T12:49:42.40504+00:00
-- url     : https://prove2.me/theorems/61f653a8-5e96-457d-a5c4-4c5a1ef4b747
-- title:
--   Courtade–Kumar proof module `CKLaneM1.ML.Population (supergroup 01 tree root)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.ML.Population (supergroup 01 tree root)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.ML.Population (supergroup 01 tree root)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.ML.Population (supergroup 01 tree root) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/ML/Population (supergroup 01 tree root).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation_s01_t0
import Definitions.Def_CK_CKLaneM1_MLPopulation_s01_t1

set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def supgrp_01 : List (List ℕ × LeafCert) :=
  sgt_01_0 ++ sgt_01_1

theorem supgrp_01_sem : ∀ x ∈ supgrp_01, SemSS (ssBox x.1) :=
  sem_append sgt_01_0_sem sgt_01_1_sem

end CKLaneM1.ML.Population


