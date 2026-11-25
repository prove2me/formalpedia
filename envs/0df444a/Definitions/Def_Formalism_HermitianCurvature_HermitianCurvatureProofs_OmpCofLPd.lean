-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OmpCofLPd
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T02:09:41.424015+00:00
-- url     : https://prove2.me/theorems/544ffa6d-a790-5a6a-9372-6e3da0e5b0d0
-- title:
--   Omp Cof LPd
-- statement:
--   Definitions and structural lemmas for Omp Cof LPd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OmpCofLPd.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementTL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HomogeneityNaturalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.TLC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TL Formalism.FourierDecayAlt.P.PartialDerivativeAlgebra
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.TLC


