-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_FiniteAdeleIdempotentOfFMulSelf
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T21:20:31.530226+00:00
-- url     : https://prove2.me/theorems/48bb2a69-ca30-4e9e-bcbf-8eaf37d8af65
-- title:
--   Finite Adele Idempotent Of FMul Self
-- statement:
--   Definitions and structural lemmas for Finite Adele Idempotent Of FMul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalCartanPairs/FiniteAdeleIdempotentOfFMulSelf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_PiNonunit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.SqPair.LCP
section Alg
variable {R : Type} [CommRing R] [StarRing R]
def e0 : Matrix (Fin 2) (Fin 2) R := diagonal ![1, 0]
end Alg
end PI.SqPair.LCP


