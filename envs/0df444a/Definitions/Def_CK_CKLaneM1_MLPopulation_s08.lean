-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_s08
-- name    : CK_CKLaneM1_MLPopulation_s08
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T06:09:55.006912+00:00
-- url     : https://prove2.me/theorems/94d0c1ca-539b-411b-b49b-4a57b2616181
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

import Definitions.Def_CK_CKLaneM1_MLPopulation_h064
import Definitions.Def_CK_CKLaneM1_MLPopulation_h065
import Definitions.Def_CK_CKLaneM1_MLPopulation_h066
import Definitions.Def_CK_CKLaneM1_MLPopulation_h067
import Definitions.Def_CK_CKLaneM1_MLPopulation_h068
import Definitions.Def_CK_CKLaneM1_MLPopulation_h069
import Definitions.Def_CK_CKLaneM1_MLPopulation_h070
import Definitions.Def_CK_CKLaneM1_MLPopulation_h071
set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def supgrp_08 : List (List ℕ × LeafCert) :=
  leafgrp_064 ++ (leafgrp_065 ++ (leafgrp_066 ++ (leafgrp_067 ++ (leafgrp_068 ++ (leafgrp_069 ++ (leafgrp_070 ++ (leafgrp_071)))))))

theorem supgrp_08_sem : ∀ x ∈ supgrp_08, SemSS (ssBox x.1) :=
  sem_append leafgrp_064_sem (sem_append leafgrp_065_sem (sem_append leafgrp_066_sem (sem_append leafgrp_067_sem (sem_append leafgrp_068_sem (sem_append leafgrp_069_sem (sem_append leafgrp_070_sem (leafgrp_071_sem)))))))

end CKLaneM1.ML.Population


