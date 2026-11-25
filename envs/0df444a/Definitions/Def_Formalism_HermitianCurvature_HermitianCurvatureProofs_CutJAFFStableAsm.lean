-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAsm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableAsm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:10:51.233646+00:00
-- url     : https://prove2.me/theorems/127c6cfe-9969-5827-9b46-d63bc3851a40
-- title:
--   Cut JAFFStable Asm
-- statement:
--   Definitions and structural lemmas for Cut JAFFStable Asm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableAsm.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStable2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS
open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS


