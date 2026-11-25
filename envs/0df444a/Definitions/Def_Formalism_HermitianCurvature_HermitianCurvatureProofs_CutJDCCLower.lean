-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:51:36.177738+00:00
-- url     : https://prove2.me/theorems/5daade3e-4e53-5516-8e7f-e9c3110ded44
-- title:
--   Cut JDCCLower
-- statement:
--   Definitions and structural lemmas for Cut JDCCLower, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDCCLower.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJD
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
namespace Formalism.FourierDecayAlt.P.CutMP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
end
end Formalism.FourierDecayAlt.P.CutMP


