-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJmuHC
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:17:38.210368+00:00
-- url     : https://prove2.me/theorems/1cc3583b-bfe0-4cc2-a2d7-b8af0bd4226a
-- title:
--   Cut Jmu HC
-- statement:
--   Definitions and structural lemmas for Cut Jmu HC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJmuHC.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.CutBP.JmuHC
open Finset
variable {n : ℕ}
def numHC (x : Fin n → ℝ) : ℝ := ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), |x a - x b|
end Formalism.FourierDecayAlt.P.CutBP.JmuHC


