-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
-- name    : Development_AutomorphicArithmetic_PrimeDiscriminants_RamDiscr
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:17.485807+00:00
-- url     : https://prove2.me/theorems/996190b7-9b30-403d-bd4d-36bae51b87e9
-- title:
--   Ram Discr
-- statement:
--   Definitions and structural lemmas for Ram Discr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/PrimeDiscriminants/RamDiscr.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SmallRam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Ideal
noncomputable section
namespace Formalism.HC
end Formalism.HC
namespace Formalism.BasicNotions.Host
variable {R : Ranks} (H : Host R)
end Formalism.BasicNotions.Host
end


