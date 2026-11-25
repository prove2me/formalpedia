-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
-- name    : Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:30.720331+00:00
-- url     : https://prove2.me/theorems/52df89c7-7067-4fe9-a47c-56c78029e055
-- title:
--   Prime Congruence Conditions
-- statement:
--   Definitions and structural lemmas for Prime Congruence Conditions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ChainSlopeWindows/PrimeCongruenceConditions.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
namespace Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
section Host
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end Host
section Real
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end Real
section Real2
variable {e q d : ℕ} [Fact q.Prime] [Fact d.Prime]
end Real2
end Formalism.LFunctionChainParameters.LBr2


