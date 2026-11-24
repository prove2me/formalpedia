-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T15:35:18.798798+00:00
-- url     : https://prove2.me/theorems/f5f14bfb-625d-47ec-bf1f-0af9ba674032
-- title:
--   Determinant Reindex
-- statement:
--   Definitions and structural lemmas for Determinant Reindex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean

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
namespace DeterminantReindex
open C2x2 CardInsertEmbedding
end DeterminantReindex
end Formalism.FourierDecayAlt.P


