-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MertensLogSum_LogFactorialEqSumLog
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:18:29.702226+00:00
-- url     : https://prove2.me/theorems/93937349-ef87-4ab8-9ffb-4c3987792603
-- title:
--   Log Factorial Eq Sum Log
-- statement:
--   Definitions and structural lemmas for Log Factorial Eq Sum Log, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MertensLogSum/LogFactorialEqSumLog.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI.PrimeLogOverPWork
open Finset ArithmeticFunction Nat
noncomputable def S (n : ℕ) : ℝ :=
  ∑ p ∈ Ioc 0 n with p.Prime, Real.log (p : ℝ) / (p : ℝ)
end PI.PrimeLogOverPWork


