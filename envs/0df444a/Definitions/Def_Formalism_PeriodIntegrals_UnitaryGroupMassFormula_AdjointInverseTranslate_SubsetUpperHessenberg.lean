-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:27:56.768672+00:00
-- url     : https://prove2.me/theorems/5812546b-8ac8-41e7-8c85-d09bded48f7f
-- title:
--   Subset Upper Hessenberg
-- statement:
--   Definitions and structural lemmas for Subset Upper Hessenberg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
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
namespace AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
end AAInvW


