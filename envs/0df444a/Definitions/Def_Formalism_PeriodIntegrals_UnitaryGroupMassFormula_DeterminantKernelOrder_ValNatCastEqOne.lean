-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelOrder_ValNatCastEqOne
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:21:05.768244+00:00
-- url     : https://prove2.me/theorems/e5d6bb4d-e742-4d3e-8785-f65afc3fb6cc
-- title:
--   Val Nat Cast Eq One
-- statement:
--   Definitions and structural lemmas for Val Nat Cast Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DeterminantKernelOrder/ValNatCastEqOne.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
namespace PI.KerIso.DetOrdW
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]
variable {E : Type} [Field E] [Algebra K E] {n : Type} [Fintype n]
end PI.KerIso.DetOrdW


