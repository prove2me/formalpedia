-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChebyshevPrimeBounds_ChebyshevPrimeBoundsLogFact
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:50.729859+00:00
-- url     : https://prove2.me/theorems/3c46a2cd-8836-4c8e-85c6-e2764f9d2e3f
-- title:
--   Chebyshev Prime Bounds Log Fact
-- statement:
--   Definitions and structural lemmas for Chebyshev Prime Bounds Log Fact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ChebyshevPrimeBounds/ChebyshevPrimeBoundsLogFact.lean

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
open Real MeasureTheory Set
def phi (t : ℝ) : ℝ := Chebyshev.theta t / (t * log t ^ 2)
def gg (t : ℝ) : ℝ := 1.56 * (t / log t ^ 2) + 0.7 * log t
def gg' (t : ℝ) : ℝ := 1.56 * (1 / log t ^ 2 - 2 / log t ^ 3) + 0.7 / t
end PI.PC


