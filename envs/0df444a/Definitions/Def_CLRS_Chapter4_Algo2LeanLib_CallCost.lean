-- Prove2me | Definitions.Def_CLRS_Chapter4_Algo2LeanLib_CallCost
-- name    : CLRS_Chapter4_Algo2LeanLib_CallCost
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:30.120984+00:00
-- url     : https://prove2.me/theorems/4051e4be-c76e-42fe-8bfa-24b90509756f
-- title:
--   Composable counter-increment contracts for Algo2Lean calls
-- statement:
--   This bundle defines and supports additive named-clock increments across a call and their composition across consecutive calls. Increments relates the final counters to the initial counters plus a supplied natural-valued vector, so costs compose even when a caller begins with nonzero counters. The definitions distinguish counter monotonicity and exact additive increments from a truncated subtraction alone.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Algo2LeanLib.CallCost, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/Algo2LeanLib/CallCost.lean

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
Clock contracts describe increments from the caller's actual initial heap.
Weighted and amortized bounds compose on the same finite call witness used
for correctness; no counter is reset and no second execution is selected.
-/

namespace Algo2LeanGenerated

/-- Every named counter is nondecreasing between the supplied heap snapshots. -/
def Heap.ClocksMonotone (before after : Heap) : Prop :=
  ∀ name, before.clocks name ≤ after.clocks name





/-- An exact clock effect permits arbitrary program-data changes and arbitrary
    initial counter values. -/
def Heap.Increments (before after : Heap) (costs : Clocks) : Prop :=
  ∀ name, after.clocks name = before.clocks name + costs name



























namespace CallCost

universe u
variable {State : Type u}











end CallCost
end Algo2LeanGenerated

end CLRS


