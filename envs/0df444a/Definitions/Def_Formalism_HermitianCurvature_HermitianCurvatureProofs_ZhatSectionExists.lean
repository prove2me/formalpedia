-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ZhatSectionExists
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T17:04:47.630868+00:00
-- url     : https://prove2.me/theorems/9b7590b2-d5ee-4e7c-ba53-524a7e17e2b9
-- title:
--   Zhat Section Exists
-- statement:
--   Definitions and structural lemmas for Zhat Section Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ZhatSectionExists.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedFrameProperty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector UnipotentSums
end Formalism.FourierDecayAlt.P


