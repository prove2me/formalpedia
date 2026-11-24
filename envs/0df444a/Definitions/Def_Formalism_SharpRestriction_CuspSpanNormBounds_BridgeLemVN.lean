-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVN
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T09:29:01.355804+00:00
-- url     : https://prove2.me/theorems/fcaa3b7e-703b-4784-b0df-cf3b77e74d68
-- title:
--   Bridge Lem VN
-- statement:
--   Definitions and structural lemmas for Bridge Lem VN, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVN.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemVN
open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne Formalism.MainNotions.BridgeLemVR
  Formalism.MainNotions.BridgeLemVC
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Formalism.MainNotions.BridgeLemVN
end


