-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:57.150613+00:00
-- url     : https://prove2.me/theorems/aab4eec4-cfe1-4cd5-b447-62bf59b7afaf
-- title:
--   EHc Change
-- statement:
--   Definitions and structural lemmas for EHc Change, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EHcChange.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Formalism.FourierDecayAlt.P.JFxE


