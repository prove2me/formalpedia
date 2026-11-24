-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UpperMinorIdentity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_UpperMinorIdentity
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:53:55.202383+00:00
-- url     : https://prove2.me/theorems/1e15f734-633f-4e2d-b44b-e0b99728df81
-- title:
--   Upper Minor Identity
-- statement:
--   Definitions and structural lemmas for Upper Minor Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UpperMinorIdentity.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
namespace Formalism.FourierDecayAlt.P
open C2x2 CardInsertEmbedding
end Formalism.FourierDecayAlt.P


