-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:46:55.127162+00:00
-- url     : https://prove2.me/theorems/0430fee5-f345-4e46-a555-c8dcf4086002
-- title:
--   Unram Bridge Holds
-- statement:
--   Definitions and structural lemmas for Unram Bridge Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnramBridgeHolds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
namespace Formalism.L2.Pj
attribute [local instance] FractionRing.liftAlgebra
end Formalism.L2.Pj


