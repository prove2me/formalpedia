-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_StdHSingleZero
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:43.169255+00:00
-- url     : https://prove2.me/theorems/324e7a9f-7e28-4b79-b7ca-10c013d9570e
-- title:
--   Std HSingle Zero
-- statement:
--   Definitions and structural lemmas for Std HSingle Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularLocalStandard/StdHSingleZero.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SatStdOfAll
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
variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}
variable {m : Type*} [Fintype m] [DecidableEq m]
end PI.UnitaryGroupMassFormula.UnimodLocStd


