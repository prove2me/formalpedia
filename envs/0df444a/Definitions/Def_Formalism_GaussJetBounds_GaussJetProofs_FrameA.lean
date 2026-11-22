-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FrameA
-- name    : Formalism_GaussJetBounds_GaussJetProofs_FrameA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:05:44.867157+00:00
-- url     : https://prove2.me/theorems/283d831f-1095-40b9-bf1c-8d15e0b64f23
-- title:
--   Frame A
-- statement:
--   Definitions and structural lemmas for Frame A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/FrameA.lean

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementK
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormDetLeOneOfEntries
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
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


