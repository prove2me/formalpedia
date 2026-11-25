-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_charsA
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_charsA
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T02:24:11.668537+00:00
-- url     : https://prove2.me/theorems/c9fd017e-1720-49d6-a97b-06e124e6e650
-- title:
--   chars A
-- statement:
--   Definitions and structural lemmas for chars A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/charsA.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_PrimRead
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CardPsiA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_TopsSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost


