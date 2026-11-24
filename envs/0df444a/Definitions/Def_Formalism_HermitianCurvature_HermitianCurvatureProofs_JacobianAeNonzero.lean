-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:29:16.890354+00:00
-- url     : https://prove2.me/theorems/64de86a2-25d2-4213-a8d3-b2158d6169ea
-- title:
--   Jacobian Ae Nonzero
-- statement:
--   Definitions and structural lemmas for Jacobian Ae Nonzero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/JacobianAeNonzero.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
namespace Formalism.FourierDecayAlt.P
namespace RootChangeOfVariables
end RootChangeOfVariables
open RootChangeOfVariables
end Formalism.FourierDecayAlt.P


