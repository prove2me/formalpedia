-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_FinprodNormEmbedding
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:44:53.57058+00:00
-- url     : https://prove2.me/theorems/da7ab80f-8c0e-4bb1-a402-0d589fc39cc5
-- title:
--   Finprod Norm Embedding
-- statement:
--   Definitions and structural lemmas for Finprod Norm Embedding, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AlgebraicValuesFinite/FinprodNormEmbedding.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_ClassSame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host
namespace PI.AlgValsFin.W
variable {L : Type} [Field L] [NumberField L]
end PI.AlgValsFin.W


