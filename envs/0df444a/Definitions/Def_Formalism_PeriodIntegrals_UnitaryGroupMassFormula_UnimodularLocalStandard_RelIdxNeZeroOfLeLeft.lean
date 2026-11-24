-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T21:31:31.373671+00:00
-- url     : https://prove2.me/theorems/b046d999-dd2c-419f-8d16-ce8d487e3484
-- title:
--   Rel Idx Ne Zero Of Le Left
-- statement:
--   Definitions and structural lemmas for Rel Idx Ne Zero Of Le Left, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RelIdxNeZeroOfLeLeft.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
section Idx
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
def smulHom (w : ℂ) : V →+ V := DistribMulAction.toAddMonoidHom V w
end Idx
section Theta
variable {a : ℕ} {b c : ℤ} {d : ℕ}
end Theta
end PI.UnitaryGroupMassFormula.UnimodLocStd


