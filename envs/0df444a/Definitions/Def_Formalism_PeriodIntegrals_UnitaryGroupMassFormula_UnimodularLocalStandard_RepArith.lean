-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepArith
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T21:55:45.412813+00:00
-- url     : https://prove2.me/theorems/fc4bc28c-4b7b-4630-ae82-445064a7ad43
-- title:
--   Rep Arith
-- statement:
--   Definitions and structural lemmas for Rep Arith, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/RepArith.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RepBasic
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
section Arith
variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)
def repKappa : ℂ := ((area (cmL a b d ha hd lam hlam) : ℝ) : ℂ)⁻¹ * (Complex.normSq lam : ℂ) * a
variable (m : Type) [Fintype m] [DecidableEq m]
end Arith
end PI.UnitaryGroupMassFormula.UnimodLocStd


