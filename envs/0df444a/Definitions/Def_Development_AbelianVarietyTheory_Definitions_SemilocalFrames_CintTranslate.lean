-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CintTranslate
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T06:04:54.559313+00:00
-- url     : https://prove2.me/theorems/159cd386-97ee-4336-bff8-d02a642de855
-- title:
--   Cint Translate
-- statement:
--   Definitions and structural lemmas for Cint Translate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CintTranslate.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_Cint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SumRefine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt
variable {W : Type} [AddCommGroup W]
end GlobalTheory.IdxInt.Model


