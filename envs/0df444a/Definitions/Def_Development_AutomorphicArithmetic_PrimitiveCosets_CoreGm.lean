-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreGm
-- name    : Development_AutomorphicArithmetic_PrimitiveCosets_CoreGm
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:26.235171+00:00
-- url     : https://prove2.me/theorems/58de84a4-e3ea-499d-bbaa-e3fc9c672015
-- title:
--   Core Gm
-- statement:
--   Definitions and structural lemmas for Core Gm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_CoreAtH
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_charsA
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_GmAEq
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_SigALe
import Definitions.Def_Development_AutomorphicArithmetic_PrimitiveCosets_hostFactsS
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChCore
import Theorems.Thm_P2M_UpperTheory_Comparison__charsA_aeb36eedc800
import Theorems.Thm_P2M_UpperTheory_Comparison__hostFactsS_fb5313d5199c

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


