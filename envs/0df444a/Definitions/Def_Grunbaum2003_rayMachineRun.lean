-- Prove2me | Definitions.Def_Grunbaum2003_rayMachineRun
-- name    : Grunbaum2003_rayMachineRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:59.676662+00:00
-- url     : https://prove2.me/theorems/e62159b6-792b-4752-8805-534b392ed303
-- title:
--   Finite ray machine execution
-- statement:
--   Iteration of the exact real transition for a finite number of steps.
-- source:
--   Branko Grünbaum, Convex Polytopes, 2nd ed. (Springer, 2003), §3.6, printed pp. 52b–52c / PDF pp. 74–75; exact-real ray-machine expression adapter; source.pdf SHA-256 070befaa8c47f043ef9da1df0705910480eb692f044d1843c9f048f3e61fecac.

import Definitions.Def_Grunbaum2003_RayInstruction
import Definitions.Def_Grunbaum2003_RayConfiguration
import Definitions.Def_Grunbaum2003_rayMachineStep

set_option autoImplicit false
open scoped BigOperators

namespace Grunbaum2003

noncomputable def rayMachineRun {d : ℕ} (program : List RayInstruction)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) :
    ℕ → RayConfiguration → Option RayConfiguration
  | 0, c => some c
  | t + 1, c => (rayMachineStep program oracle c).bind (rayMachineRun program oracle t)

end Grunbaum2003


