-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:14:48.690303+00:00
-- url     : https://prove2.me/theorems/3ab876f2-cbef-4f4b-8f85-5a5c122132a1
-- title:
--   Hermitian Form Flag Vector
-- statement:
--   Definitions and structural lemmas for Hermitian Form Flag Vector, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFlagVector.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
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
namespace C2x5
variable {k r : ℕ}
end C2x5
open C2x5
end Formalism.FourierDecayAlt.P


