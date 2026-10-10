-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveRelocation
-- name    : IntMul_EndParkRecursiveRelocation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T05:06:32.037142+00:00
-- url     : https://prove2.me/theorems/b96df2b3-4f2d-4815-8f70-f429679414a9
-- title:
--   Relative physical window translations for arbitrary recursive child frames
-- source:
--   Original native-to-interior recursive frame relocation interface. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Definitions.Def_IntMul_TraceRelocation

namespace IntMul.EndParkRecursiveRelocation

/-- Relative translations from the unit-offset native body windows into
arbitrary positive child bank, shared-buffer and continuation-stack windows. -/
def shifts (M : MultitapeTM) (rho sigma : ℕ) (offset : Fin M.k → ℕ) (i : Fin (M.k+3)) : ℕ :=
  if h : i.val < M.k+2 then
    if hw : 2 ≤ i.val then offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)-1
    else if i.val=1 then sigma-1 else 0
  else rho-1

end IntMul.EndParkRecursiveRelocation


