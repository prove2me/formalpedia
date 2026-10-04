-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_h069
-- name    : CK_CKLaneM1_MLPopulation_h069
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T04:08:25.604889+00:00
-- url     : https://prove2.me/theorems/4c37db67-d6d0-4e35-bc08-d8eabd8acee7
-- title:
--   Courtade–Kumar proof module `CKLaneM1.MLPopulation (proof part: shard group)` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneM1.MLPopulation (proof part: shard group)` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneM1.MLPopulation (proof part: shard group)` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneM1.MLPopulation (proof part: shard group) (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneM1/MLPopulation (proof part: shard group).lean)

import Definitions.Def_CK_CKLaneM1_MLPopulation_q00_q00
import Definitions.Def_CK_CKLaneM1_Pop_S0267__4
set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def leafgrp_069 : List (List ℕ × LeafCert) :=
  Pop.S0267.leaves ++ (Pop.S0268.leaves ++ (Pop.S0269.leaves ++ (Pop.S0270.leaves)))

theorem leafgrp_069_sem : ∀ x ∈ leafgrp_069, SemSS (ssBox x.1) :=
  sem_append Pop.S0267.sem (sem_append Pop.S0268.sem (sem_append Pop.S0269.sem (Pop.S0270.sem)))

end CKLaneM1.ML.Population


