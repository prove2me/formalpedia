-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
-- name    : Formalism_GaussJetBounds_GaussJetProofs_PureCrossTermWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:50.942265+00:00
-- url     : https://prove2.me/theorems/3c57608e-b050-49c0-9517-f42356ad18ba
-- title:
--   Pure Cross Term Weight
-- statement:
--   Definitions and structural lemmas for Pure Cross Term Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/PureCrossTermWeight.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
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
universe u v w
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section SlopeTestRemainingChoices
variable {K : Type u} [NormedField K] {ι : Type v}
variable [IsUltrametricDist K]
end SlopeTestRemainingChoices
end Formalism.DworkPowerSeriesWeights


