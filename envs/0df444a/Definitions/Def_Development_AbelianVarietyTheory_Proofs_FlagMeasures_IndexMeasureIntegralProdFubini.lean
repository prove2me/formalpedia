-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_IndexMeasureIntegralProdFubini
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:33.091465+00:00
-- url     : https://prove2.me/theorems/e7d535d9-ebb9-4809-84b1-4eafba68bdb6
-- title:
--   Index Measure Integral Prod Fubini
-- statement:
--   Definitions and structural lemmas for Index Measure Integral Prod Fubini, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IndexMeasureIntegralProdFubini.lean

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
open GlobalTheory.IdxInt
open scoped Pointwise Classical
namespace GlobalTheory.IdxInt.Fubini
variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']
end GlobalTheory.IdxInt.Fubini


