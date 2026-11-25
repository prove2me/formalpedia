-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutNFApxDomThQ
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:06.731867+00:00
-- url     : https://prove2.me/theorems/bdb792ce-ea43-5c47-9221-ca50adb7c52f
-- title:
--   Cut NFApx Dom Th Q
-- statement:
--   Definitions and structural lemmas for Cut NFApx Dom Th Q, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutNFApxDomThQ.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDCCLower
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
namespace Formalism.FourierDecayAlt.P.CutBP
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
end
end Formalism.FourierDecayAlt.P.CutBP


