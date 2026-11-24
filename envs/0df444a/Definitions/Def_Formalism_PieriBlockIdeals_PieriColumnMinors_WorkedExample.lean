-- Prove2me | Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
-- name    : Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:53:57.941927+00:00
-- url     : https://prove2.me/theorems/522e4a86-6f25-4808-8348-84386b854d82
-- title:
--   Worked Example
-- statement:
--   Definitions and structural lemmas for Worked Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
def exampleParamsAlt : LogSmallConstantBounds.Par :=
  {k := 1, m := 1, t := 6, f := 1, n := 1, Nr := 7, L := 60, x := 4, b' := 40000000, η := 6, S := 4}
end Formalism.CohomologicalDescent.WorkedExample


