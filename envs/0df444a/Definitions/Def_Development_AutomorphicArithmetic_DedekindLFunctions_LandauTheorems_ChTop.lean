-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop
-- name    : Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChTop
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:14:37.275049+00:00
-- url     : https://prove2.me/theorems/9e44338b-e8b9-4bc2-8b9c-18b4852fab33
-- title:
--   Ch Top
-- statement:
--   Definitions and structural lemmas for Ch Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
end Deduction
end


