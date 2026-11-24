-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeDivOfMulEqLe
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LeDivOfMulEqLe
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:52.0368+00:00
-- url     : https://prove2.me/theorems/aa138264-94c8-411d-9214-b80e06618375
-- title:
--   Le Div Of Mul Eq Le
-- statement:
--   Definitions and structural lemmas for Le Div Of Mul Eq Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LeDivOfMulEqLe.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryMinorBounds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UpperMinorIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetSubmatrixUnitriangularEqOne
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
open C2x2 EntryMinorBounds
end Formalism.FourierDecayAlt.P


