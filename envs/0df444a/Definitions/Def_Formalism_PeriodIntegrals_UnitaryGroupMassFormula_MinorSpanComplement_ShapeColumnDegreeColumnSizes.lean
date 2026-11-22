-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ShapeColumnDegreeColumnSizes
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:12:58.900039+00:00
-- url     : https://prove2.me/theorems/2a3b9396-7bfd-4d55-b903-483eb0abdc84
-- title:
--   Shape Column Degree Column Sizes
-- statement:
--   Definitions and structural lemmas for Shape Column Degree Column Sizes, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ShapeColumnDegreeColumnSizes.lean

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace PI.MSC
def sz0 (ν : YoungDiagram) : Fin (ν.rowLen 0) → ℕ := fun c => ν.colLen c
theorem hsz0 (ν : YoungDiagram) : ∀ c, sz0 ν c ≤ ν.colLen 0 := fun c => ν.colLen_anti 0 c (Nat.zero_le _)
def nuR (ν : YoungDiagram) : Fin (ν.colLen 0) → ℕ := fun t => ν.rowLen t
end PI.MSC


