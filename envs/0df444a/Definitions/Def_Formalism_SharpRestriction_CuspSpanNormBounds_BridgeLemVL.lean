-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLemVL
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:36:29.830564+00:00
-- url     : https://prove2.me/theorems/8e62a758-aadd-4c3a-8c81-705e9c5460c8
-- title:
--   Bridge Lem VL
-- statement:
--   Definitions and structural lemmas for Bridge Lem VL, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/BridgeLemVL.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemVL
open NumberField Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def Z2 : ℝ := ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹
end Formalism.MainNotions.BridgeLemVL
end


