-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_Residue
-- name    : Formalism_PeriodIntegrals_Residue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:04.125083+00:00
-- url     : https://prove2.me/theorems/0faeb6c7-75d3-4ab9-97d4-c9fd29a361f7
-- title:
--   Residue
-- statement:
--   Definitions and structural lemmas for Residue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/Residue.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI
def ResidueBound : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E], 2 ≤ Module.finrank ℚ E →
    dedekindZeta_residue E ≤
      (C * Real.log (((|discr E| : ℤ) : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ E))) ^ Module.finrank ℚ E
end PI


