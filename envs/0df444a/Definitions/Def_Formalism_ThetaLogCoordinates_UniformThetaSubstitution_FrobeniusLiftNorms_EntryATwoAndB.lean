-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
-- name    : Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_EntryATwoAndB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:51:48.930062+00:00
-- url     : https://prove2.me/theorems/2ed68571-85c6-4903-8459-2e8528a2e250
-- title:
--   Entry ATwo And B
-- statement:
--   Definitions and structural lemmas for Entry ATwo And B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/EntryATwoAndB.lean

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GrowthSums_StatementG
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
namespace ParitySumsOverFilteredPairs
variable {ν r0 r1 E : ℕ}
def iN (β : KapI ν r1 E →₀ ℕ) (s : ZMod (2 * ν)) (e' : ℕ) : ℕ :=
  if h : e' < E then ∑ b, β (s, ⟨e', h⟩, b) else 0
end ParitySumsOverFilteredPairs
open ParitySumsOverFilteredPairs
end Formalism.InvariantFactorPaths.G7


