-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
-- name    : Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:47:38.652805+00:00
-- url     : https://prove2.me/theorems/b28af269-6ab5-4524-b2c0-c9e97b1a2b9c
-- title:
--   One Letter Unramified Bound
-- statement:
--   Definitions and structural lemmas for One Letter Unramified Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
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
universe u v
namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds
end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds


