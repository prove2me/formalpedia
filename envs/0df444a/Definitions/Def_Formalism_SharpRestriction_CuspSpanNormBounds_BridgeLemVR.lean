-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVR
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T09:24:35.583848+00:00
-- url     : https://prove2.me/theorems/0b19b0ec-6a09-49f9-bb6a-0cb90022a04f
-- title:
--   Bridge Lem VR
-- statement:
--   Definitions and structural lemmas for Bridge Lem VR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVR.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMassConstOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemVR
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Formalism.MainNotions.BridgeLemVR
end


