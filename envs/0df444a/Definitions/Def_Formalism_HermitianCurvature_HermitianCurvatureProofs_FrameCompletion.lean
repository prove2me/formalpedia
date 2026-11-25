-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:55:28.871423+00:00
-- url     : https://prove2.me/theorems/3381cbca-65ae-50da-a882-1b265eca69c8
-- title:
--   Frame Completion
-- statement:
--   Definitions and structural lemmas for Frame Completion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FrameCompletion.lean

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace HermitianFormSums
variable {k r : ℕ}
end HermitianFormSums
end Formalism.FourierDecayAlt.P


