-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Generic
-- name    : Formalism_GaussJetBounds_GaussJetProofs_Generic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:10:54.778909+00:00
-- url     : https://prove2.me/theorems/3e805b0a-9194-49d2-9ee9-67f9c8a798f1
-- title:
--   Generic
-- statement:
--   Definitions and structural lemmas for Generic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Generic.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementM
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
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
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
end Formalism.DworkPowerSeriesWeights


