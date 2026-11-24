-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RightDerivativeRulePsi
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T20:19:53.255801+00:00
-- url     : https://prove2.me/theorems/513ac2c3-a8ef-4209-8d31-2faeab144e34
-- title:
--   Right Derivative Rule Psi
-- statement:
--   Definitions and structural lemmas for Right Derivative Rule Psi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RightDerivativeRulePsi.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
section dp
variable {k r : ℕ} (z' : Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1))
end dp
end Formalism.FourierDecayAlt.P.SignAntidiagonal


