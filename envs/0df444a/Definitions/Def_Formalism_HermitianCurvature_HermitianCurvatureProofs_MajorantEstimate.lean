-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:37.495274+00:00
-- url     : https://prove2.me/theorems/72fc06b4-6ad3-4ac7-8690-949cbfef551c
-- title:
--   Majorant Estimate
-- statement:
--   Definitions and structural lemmas for Majorant Estimate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MajorantEstimate.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace C2x6
open C2x5
variable {k r : ℕ}
end C2x6
open C2x5 C2x6
end Formalism.FourierDecayAlt.P


