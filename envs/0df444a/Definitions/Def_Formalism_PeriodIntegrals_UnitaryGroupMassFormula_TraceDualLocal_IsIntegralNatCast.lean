-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralNatCast
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:47.014389+00:00
-- url     : https://prove2.me/theorems/9e0661cb-ecda-4680-9dcf-a31ac2ca3312
-- title:
--   Is Integral Nat Cast
-- statement:
--   Definitions and structural lemmas for Is Integral Nat Cast, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TraceDualLocal/IsIntegralNatCast.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TraceDualLocal_IsIntegralOfTmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.TrDualLocW
open NumberField
open scoped TensorProduct
variable {K : Type} [Field K] [NumberField K] {ℓ : ℕ} [Fact ℓ.Prime]
end PI.TrDualLocW


