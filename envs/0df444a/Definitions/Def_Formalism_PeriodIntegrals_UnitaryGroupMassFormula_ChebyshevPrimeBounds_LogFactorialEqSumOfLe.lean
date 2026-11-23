-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_LogFactorialEqSumOfLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:52.970581+00:00
-- url     : https://prove2.me/theorems/f3a096ed-f828-4572-9ba3-352b3146386d
-- title:
--   Log Factorial Eq Sum Of Le
-- statement:
--   Definitions and structural lemmas for Log Factorial Eq Sum Of Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/LogFactorialEqSumOfLe.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_PrimeCountBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.PC
open Finset Real
open ArithmeticFunction hiding log id
open scoped Nat Chebyshev ArithmeticFunction.zeta
def chE (q : ℕ) : ℝ :=
  (q : ℝ) - ((q / 2 : ℕ) : ℝ) - ((q / 3 : ℕ) : ℝ) - ((q / 5 : ℕ) : ℝ) + ((q / 30 : ℕ) : ℝ)
end PI.PC


