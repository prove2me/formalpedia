-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_h074
-- name    : CK_CKLaneM1_MLPopulation_h074
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T03:25:56.190433+00:00
-- url     : https://prove2.me/theorems/f130d469-f4be-45fa-84a4-0ece2f3a21a2
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
import Definitions.Def_CK_CKLaneM1_Pop_S0289__4
set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def leafgrp_074 : List (List ℕ × LeafCert) :=
  Pop.S0289.leaves ++ (Pop.S0290.leaves ++ (Pop.S0291.leaves ++ (Pop.S0292.leaves)))

theorem leafgrp_074_sem : ∀ x ∈ leafgrp_074, SemSS (ssBox x.1) :=
  sem_append Pop.S0289.sem (sem_append Pop.S0290.sem (sem_append Pop.S0291.sem (Pop.S0292.sem)))

end CKLaneM1.ML.Population


