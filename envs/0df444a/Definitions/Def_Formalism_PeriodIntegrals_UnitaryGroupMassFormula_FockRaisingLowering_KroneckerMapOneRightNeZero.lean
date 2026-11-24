-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockRaisingLowering_KroneckerMapOneRightNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:25.922967+00:00
-- url     : https://prove2.me/theorems/e5171d8b-38ec-433f-91ad-7c4696966780
-- title:
--   Kronecker Map One Right Ne Zero
-- statement:
--   Definitions and structural lemmas for Kronecker Map One Right Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockRaisingLowering/KroneckerMapOneRightNeZero.lean

import Mathlib
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
open Matrix
namespace FockRL
def jsgn {p q : ℕ} : FockH1Action.Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)
end FockRL


