-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_NotInert
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T18:31:27.209137+00:00
-- url     : https://prove2.me/theorems/c1810760-552e-4d63-979f-0e6112034789
-- title:
--   Not Inert
-- statement:
--   Definitions and structural lemmas for Not Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/NotInert.lean

import Definitions.Def_Formalism_LocalRingCardinality_HostCls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HC
namespace Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R) {p : ℕ}
end Formalism.BasicNotions.Host


