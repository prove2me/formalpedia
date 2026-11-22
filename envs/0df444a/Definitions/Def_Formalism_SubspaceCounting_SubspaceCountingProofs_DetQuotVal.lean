-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_DetQuotVal
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:30:51.527529+00:00
-- url     : https://prove2.me/theorems/5c4d3ba1-01e9-4db0-8f08-c2aea6871cfb
-- title:
--   Det Quot Val
-- statement:
--   Definitions and structural lemmas for Det Quot Val, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetQuotVal.lean

import Definitions.Def_Formalism_SubspaceCounting_DetQuotVal
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
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
namespace Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP
variable {K ι : Type} [Field K] [DecidableEq ι]
end Formalism.G0.DetQuotValP


