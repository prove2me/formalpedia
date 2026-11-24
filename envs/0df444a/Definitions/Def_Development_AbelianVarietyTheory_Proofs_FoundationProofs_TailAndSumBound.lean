-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_TailAndSumBound
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:58:52.604949+00:00
-- url     : https://prove2.me/theorems/6ed544a1-b6ff-4f69-b608-486d6e0aca08
-- title:
--   Tail And Sum Bound
-- statement:
--   Definitions and structural lemmas for Tail And Sum Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TailAndSumBound.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_KroneckerReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2IntegralityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
namespace GlobalTheory.GoodCharacterTail
open Formalism.HermitianLattices.GL2PrimeSums
end GlobalTheory.GoodCharacterTail


