-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:04:25.303235+00:00
-- url     : https://prove2.me/theorems/64ede174-354c-5002-b50a-53e0d9d0d7b0
-- title:
--   Cut JDHat Poly OK
-- statement:
--   Definitions and structural lemmas for Cut JDHat Poly OK, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatPolyOK.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP
noncomputable section
open scoped ContDiff
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end
end Formalism.FourierDecayAlt.P.CutMP


