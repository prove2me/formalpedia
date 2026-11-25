-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ChrBij
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_ChrBij
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:01:59.10581+00:00
-- url     : https://prove2.me/theorems/02671985-b8bb-5771-9287-46fc168f20e4
-- title:
--   Chr Bij
-- statement:
--   Definitions and structural lemmas for Chr Bij, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/ChrBij.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_ToEBij
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


