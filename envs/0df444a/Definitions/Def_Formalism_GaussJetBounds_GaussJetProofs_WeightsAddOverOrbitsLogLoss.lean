-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
-- name    : Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitsLogLoss
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:50.012361+00:00
-- url     : https://prove2.me/theorems/b051d781-8ab2-4ca8-bd26-e2e8c259ffc6
-- title:
--   Weights Add Over Orbits Log Loss
-- statement:
--   Definitions and structural lemmas for Weights Add Over Orbits Log Loss, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/WeightsAddOverOrbitsLogLoss.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementO
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LemmaRA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbits
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
end Formalism.DworkPowerSeriesWeights


