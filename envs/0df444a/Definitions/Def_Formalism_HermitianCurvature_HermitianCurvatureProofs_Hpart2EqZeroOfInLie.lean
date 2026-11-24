-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_Hpart2EqZeroOfInLie
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T18:00:28.293649+00:00
-- url     : https://prove2.me/theorems/6f49985f-6b28-4c7a-b08e-9b539c7a5408
-- title:
--   Hpart2 Eq Zero Of In Lie
-- statement:
--   Definitions and structural lemmas for Hpart2 Eq Zero Of In Lie, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Hpart2EqZeroOfInLie.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BridgeQminor
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
def Psi (D : Mat k r →L[ℝ] E) (g Z : Mat k r) : E :=
  D (g * hpart1 (Hpk k r) Z) + Complex.I • D (g * hpart2 (Hpk k r) Z)
end Formalism.FourierDecayAlt.P.JFxE


