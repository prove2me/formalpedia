-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:49:11.40277+00:00
-- url     : https://prove2.me/theorems/36b0cb02-8522-496a-bb19-bb091463fc3b
-- title:
--   Adjoint Functional Holds
-- statement:
--   Definitions and structural lemmas for Adjoint Functional Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
namespace Formalism.QuantumDeterminants
variable {m : ℕ}
def uW (l : Fin m) (x : Fin m → ℂ) : ℂ := x l * (((∏ k, Complex.normSq (x k))⁻¹ : ℝ) : ℂ)
end Formalism.QuantumDeterminants


