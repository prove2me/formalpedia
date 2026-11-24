-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:29:52.254872+00:00
-- url     : https://prove2.me/theorems/3720b99a-0721-49bc-a92f-d98cfba87db4
-- title:
--   Lower Parabolic Coordinates
-- statement:
--   Definitions and structural lemmas for Lower Parabolic Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LowerParabolicCoordinates.lean

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
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
namespace C2x2
variable {m : ℕ}
end C2x2
open C2x2
end Formalism.FourierDecayAlt.P


