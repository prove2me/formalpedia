-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T16:55:55.079809+00:00
-- url     : https://prove2.me/theorems/de56b0e0-16ff-4c38-beb9-3ee6295f7537
-- title:
--   First Peeling Minor Mem Ideal
-- statement:
--   Definitions and structural lemmas for First Peeling Minor Mem Ideal, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants
section peel
variable {A : Type} [Ring A] [Algebra ℂ A]
end peel
def pe (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨min p (2 * r + k), by omega⟩
def ps (k r p : ℕ) : Fin (2 * r + k + 1) := ⟨2 * r + k - p, by omega⟩
end Formalism.FourierDecayAlt.P.SignAntidiagonal


