-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_PackLem
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_PackLem
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T13:14:10.582345+00:00
-- url     : https://prove2.me/theorems/f030d85b-0a8d-427a-a763-3dce1c029c55
-- title:
--   Pack Lem
-- statement:
--   Definitions and structural lemmas for Pack Lem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/PackLem.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_BoxBoundAlt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Metric Module
namespace PI.UnitaryGroupMassFormula.LCG
def matVec {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) : EuclideanSpace ℂ (Fin N × Fin N) :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)
end PI.UnitaryGroupMassFormula.LCG
end


