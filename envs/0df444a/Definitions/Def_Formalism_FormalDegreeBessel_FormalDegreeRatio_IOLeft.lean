-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:29:22.191797+00:00
-- url     : https://prove2.me/theorems/d2e59d0d-3a16-4d24-8241-9fc77a59c74f
-- title:
--   IOLeft
-- statement:
--   Definitions and structural lemmas for IOLeft, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
namespace Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.QuantumDeterminants


