-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:54:24.392799+00:00
-- url     : https://prove2.me/theorems/e2fe0c28-5df7-4234-a0d6-99245f7f5664
-- title:
--   Stabilizer Antidiagonal Exact
-- statement:
--   Definitions and structural lemmas for Stabilizer Antidiagonal Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
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
open C2x2
end Formalism.FourierDecayAlt.P


