-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCRadSpSmooth
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCRadSpSmooth
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:55:22.179071+00:00
-- url     : https://prove2.me/theorems/90524a12-c70d-4405-818a-803e6d6974a0
-- title:
--   Cut GCRad Sp Smooth
-- statement:
--   Definitions and structural lemmas for Cut GCRad Sp Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCRadSpSmooth.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeGRawSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


