-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableGerm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAFFStableGerm
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T05:13:10.38982+00:00
-- url     : https://prove2.me/theorems/a94e3a8b-613e-428f-9da9-c2c166d5f6dc
-- title:
--   Cut JAFFStable Germ
-- statement:
--   Definitions and structural lemmas for Cut JAFFStable Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAFFStableGerm.lean

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
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section germ
variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
end germ
end Formalism.FourierDecayAlt.P.CutMP.JA.FFS


