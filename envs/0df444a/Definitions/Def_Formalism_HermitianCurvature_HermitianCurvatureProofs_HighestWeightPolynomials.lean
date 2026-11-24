-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:09:52.068542+00:00
-- url     : https://prove2.me/theorems/66d346a7-6c64-4b29-8e49-945f23df6a0c
-- title:
--   Highest Weight Polynomials
-- statement:
--   Definitions and structural lemmas for Highest Weight Polynomials, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HighestWeightPolynomials.lean

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
section mod
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end mod
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr HighestWeightPolynomials
end Formalism.FourierDecayAlt.P


