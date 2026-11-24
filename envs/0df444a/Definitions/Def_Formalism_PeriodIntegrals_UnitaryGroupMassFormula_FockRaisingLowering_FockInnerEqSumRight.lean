-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_FockInnerEqSumRight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:19.670828+00:00
-- url     : https://prove2.me/theorems/7e103799-be32-4681-9aea-b59da520b00b
-- title:
--   Fock Inner Eq Sum Right
-- statement:
--   Definitions and structural lemmas for Fock Inner Eq Sum Right, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/FockInnerEqSumRight.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_SameSign
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace FockRaiseLowInner
open MvPolynomial FockH1Action
variable {σ : Type*}
def wt (α : σ →₀ ℕ) : ℂ := α.prod (fun _ k => (k.factorial : ℂ))
end FockRaiseLowInner


