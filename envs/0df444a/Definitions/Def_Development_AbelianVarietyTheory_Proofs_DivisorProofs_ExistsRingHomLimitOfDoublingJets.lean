-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJets
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomLimitOfDoublingJets
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:57.251647+00:00
-- url     : https://prove2.me/theorems/d1df48ac-655b-45e2-9ed8-bdc948b55f99
-- title:
--   Exists Ring Hom Limit Of Doubling Jets
-- statement:
--   Definitions and structural lemmas for Exists Ring Hom Limit Of Doubling Jets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRingHomLimitOfDoublingJets.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivCompM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
namespace GlobalTheory.Nef.PathJet
open PowerSeries
end GlobalTheory.Nef.PathJet


