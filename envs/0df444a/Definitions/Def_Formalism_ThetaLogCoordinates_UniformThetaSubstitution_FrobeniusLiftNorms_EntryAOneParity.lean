-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryAOneParity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:51:31.827151+00:00
-- url     : https://prove2.me/theorems/0ebfb80b-3788-4d52-ad86-1574ec4d6e63
-- title:
--   Entry AOne Parity
-- statement:
--   Definitions and structural lemmas for Entry AOne Parity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryAOneParity.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact)
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace ValuationParity
def par (ν : ℕ) : ZMod (2 * ν) →+* ZMod 2 := ZMod.castHom (Dvd.intro ν rfl) (ZMod 2)
end ValuationParity
end Formalism.InvariantFactorPaths.G7


