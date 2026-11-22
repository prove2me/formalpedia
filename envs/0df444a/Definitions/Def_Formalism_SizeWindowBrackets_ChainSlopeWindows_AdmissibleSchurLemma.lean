-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:18:33.525273+00:00
-- url     : https://prove2.me/theorems/74451ae9-ec66-4130-a3cf-c0479321362b
-- title:
--   Admissible Schur Lemma
-- statement:
--   Definitions and structural lemmas for Admissible Schur Lemma, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/AdmissibleSchurLemma.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
def gT (y : ℝ) : ℝ := (Real.log y + 1) / y
end
end Formalism.LFunctionChainParameters.DeficitSplitLemmas


