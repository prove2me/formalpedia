-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_Columns_GFamS
-- name    : Formalism_LocalToGlobal_Columns_GFamS
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:12:06.543477+00:00
-- url     : https://prove2.me/theorems/31375b54-ac58-4bed-b346-3346bd4a232a
-- title:
--   GFam S
-- statement:
--   Definitions and structural lemmas for GFam S, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GFamS.lean

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Col
structure GFamS (K : Type) [Field K] [NumberField K] [StarRing K] extends GFam K where

  sec : ∀ b, (toGFam.mem b).Sec
end Formalism.L2.Col


