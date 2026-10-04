-- Prove2me | Definitions.Def_CK_CKLaneM1_MLPopulation_s06
-- name    : CK_CKLaneM1_MLPopulation_s06
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-10-04T10:10:36.43245+00:00
-- url     : https://prove2.me/theorems/9847abb9-a877-4c26-baba-3e2583e2d941
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

import Definitions.Def_CK_CKLaneM1_MLPopulation_h048
import Definitions.Def_CK_CKLaneM1_MLPopulation_h049
import Definitions.Def_CK_CKLaneM1_MLPopulation_h050
import Definitions.Def_CK_CKLaneM1_MLPopulation_h051
import Definitions.Def_CK_CKLaneM1_MLPopulation_h052
import Definitions.Def_CK_CKLaneM1_MLPopulation_h053
import Definitions.Def_CK_CKLaneM1_MLPopulation_h054
import Definitions.Def_CK_CKLaneM1_MLPopulation_h055
set_option autoImplicit false
set_option maxRecDepth 100000
namespace CKLaneM1.ML.Population
open CKLaneM1.ML
def supgrp_06 : List (List ℕ × LeafCert) :=
  leafgrp_048 ++ (leafgrp_049 ++ (leafgrp_050 ++ (leafgrp_051 ++ (leafgrp_052 ++ (leafgrp_053 ++ (leafgrp_054 ++ (leafgrp_055)))))))

theorem supgrp_06_sem : ∀ x ∈ supgrp_06, SemSS (ssBox x.1) :=
  sem_append leafgrp_048_sem (sem_append leafgrp_049_sem (sem_append leafgrp_050_sem (sem_append leafgrp_051_sem (sem_append leafgrp_052_sem (sem_append leafgrp_053_sem (sem_append leafgrp_054_sem (leafgrp_055_sem)))))))

end CKLaneM1.ML.Population


