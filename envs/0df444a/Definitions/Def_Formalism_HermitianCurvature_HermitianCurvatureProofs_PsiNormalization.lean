-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PsiNormalization
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:52:35.359957+00:00
-- url     : https://prove2.me/theorems/ba5a9a08-9bf8-4f0b-bbcf-04180069cacd
-- title:
--   Psi Normalization
-- statement:
--   Definitions and structural lemmas for Psi Normalization, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PsiNormalization.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
namespace Formalism.FourierDecayAlt.P.BesselCapelliCommutation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.BesselCapelliCommutation
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


