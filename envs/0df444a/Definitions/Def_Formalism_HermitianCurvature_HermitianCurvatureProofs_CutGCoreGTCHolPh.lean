-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCHolPh
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T05:54:17.158835+00:00
-- url     : https://prove2.me/theorems/c22c55c9-adb3-4f15-b18a-89ffa4a62f3b
-- title:
--   Cut GCore GTCHol Ph
-- statement:
--   Definitions and structural lemmas for Cut GCore GTCHol Ph, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCHolPh.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ph
def AnnT (TT : ℝ) : Set ℂ := {ζ : ℂ | TT < Complex.normSq ζ}
end Ph
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC


