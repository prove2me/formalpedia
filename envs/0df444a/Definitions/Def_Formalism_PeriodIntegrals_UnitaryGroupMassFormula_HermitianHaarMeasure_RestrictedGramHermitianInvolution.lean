-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_RestrictedGramHermitianInvolution
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:49:58.088521+00:00
-- url     : https://prove2.me/theorems/4e592a62-3ec4-4fbd-8c68-c004cae298bc
-- title:
--   Restricted Gram Hermitian Involution
-- statement:
--   Definitions and structural lemmas for Restricted Gram Hermitian Involution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/RestrictedGramHermitianInvolution.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.QnHermHaar
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
end PI.QnHermHaar


