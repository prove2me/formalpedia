-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SubMemDifferentIdeal
-- name    : Development_AbelianVarietyTheory_Proofs_FlagMeasures_SubMemDifferentIdeal
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T22:05:15.585196+00:00
-- url     : https://prove2.me/theorems/6ecd0f20-01fa-40f3-a9b9-b21560b6180f
-- title:
--   Sub Mem Different Ideal
-- statement:
--   Definitions and structural lemmas for Sub Mem Different Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SubMemDifferentIdeal.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal
namespace GlobalTheory.CMDiscrSq
open Polynomial
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
end GlobalTheory.CMDiscrSq


