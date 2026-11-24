-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_HermitianAlgebraGeneration
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_HermitianAlgebraGeneration
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:10:36.038032+00:00
-- url     : https://prove2.me/theorems/0fb40975-17fa-49f6-8a2a-3dc395aa5e7f
-- title:
--   Hermitian Algebra Generation
-- statement:
--   Definitions and structural lemmas for Hermitian Algebra Generation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/HermitianAlgebraGeneration.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_GeneralSecondMinorExpansion
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
open Formalism.REAL Formalism.FourierDecayAlt.Q
end PI.QnHermHaar


