-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeGRawSmooth
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeGRawSmooth
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:11:39.460282+00:00
-- url     : https://prove2.me/theorems/635c50a8-8b12-5eda-9487-1e52ee5b93b9
-- title:
--   Cut Gauge GRaw Smooth
-- statement:
--   Definitions and structural lemmas for Cut Gauge GRaw Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeGRawSmooth.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnTrSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NFRadRedA
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
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P.CutMP.Gauge


