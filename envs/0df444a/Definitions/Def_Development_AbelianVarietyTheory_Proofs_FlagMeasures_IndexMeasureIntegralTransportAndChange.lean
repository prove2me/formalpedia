-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChange
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralTransportAndChange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T06:19:57.775428+00:00
-- url     : https://prove2.me/theorems/fe7883e2-f4b5-40f9-9f9f-814062b55a17
-- title:
--   Index Measure Integral Transport And Change
-- statement:
--   Definitions and structural lemmas for Index Measure Integral Transport And Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralTransportAndChange.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.IdxInt
open scoped Pointwise Classical
namespace GlobalTheory.IdxInt.Transport
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
end GlobalTheory.IdxInt.Transport


