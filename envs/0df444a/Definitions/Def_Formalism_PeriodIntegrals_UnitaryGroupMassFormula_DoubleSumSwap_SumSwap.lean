-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DoubleSumSwap_SumSwap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:34.409848+00:00
-- url     : https://prove2.me/theorems/91fb33da-f2a8-4e91-a5ae-212f095db503
-- title:
--   Sum Swap
-- statement:
--   Definitions and structural lemmas for Sum Swap, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/DoubleSumSwap/SumSwap.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
namespace HSDoublingWork
open Formalism.MainNotions.Ext.CutB
variable {N : ℕ} (ε : Fin N → Bool) (z : cBNC ε → ℂ)
noncomputable def U (x : Fin N × Fin N) : ℝ :=
  if h : x.1 < x.2 ∧ ε x.1 ≠ ε x.2 then ‖z ⟨x, h⟩‖ ^ 2 else 0
end HSDoublingWork


