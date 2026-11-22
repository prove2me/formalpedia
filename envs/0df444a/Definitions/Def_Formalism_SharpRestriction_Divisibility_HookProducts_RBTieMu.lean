-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
-- name    : Formalism_SharpRestriction_Divisibility_HookProducts_RBTieMu
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:10.120913+00:00
-- url     : https://prove2.me/theorems/152c1cd4-f252-466b-9d34-cbe6d3e7abfa
-- title:
--   RBTie Mu
-- statement:
--   Definitions and structural lemmas for RBTie Mu, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/HookProducts/RBTieMu.lean

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieOp
import Definitions.Def_Formalism_SharpRestriction_Divisibility_HookProducts_RBTieSlope
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField Module
noncomputable section
namespace Formalism.MainNotions.DIV.HookProducts.RBTie
section Mu
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end Mu
end Formalism.MainNotions.DIV.HookProducts.RBTie


