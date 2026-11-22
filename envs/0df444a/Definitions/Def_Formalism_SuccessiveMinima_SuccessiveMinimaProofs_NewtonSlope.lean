-- Prove2me | Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
-- name    : Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:01.05612+00:00
-- url     : https://prove2.me/theorems/89a59356-b92f-4d61-b1a6-faf5dc3e88e8
-- title:
--   Newton Slope
-- statement:
--   Definitions and structural lemmas for Newton Slope, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NewtonSlope.lean

import Definitions.Def_Formalism_SuccessiveMinima_StatementNP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FN
open Filter Topology
variable {K : Type*} [NormedField K]
end Formalism.FN


