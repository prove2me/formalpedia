-- Prove2me | Definitions.Def_HSElemKernel_outputOf
-- name    : HSElemKernel_outputOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:24:31.548188+00:00
-- url     : https://prove2.me/theorems/7ff9290c-b3e7-447f-91ae-dafb7b81f756
-- title:
--   Instance output of a kernel
-- statement:
--   The **instance output** of a run with final memory $\mathrm{mem}$ is the output list (length in cell $0$, entries in cells $1, 2, \dots$) decoded by the strict instance decoder; it is undefined (*none*) when the output is not the code of an instance.
--
--   A kernel "maps an instance $(I, k)$ to an instance $(I', k')$" (Section 3.1); this is how the mission reads $(I', k')$ from the machine.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3.1, p.6

import Mathlib
import Definitions.Def_HSElemKernel_decodeInst
import Definitions.Def_HSElemKernel_outputList

namespace HSElemKernel

/-- The `d`-Hitting Set instance a kernel outputs in memory `mem`: the output list
(`outputList`: length in cell `0`, entries in cells `1, …`) decoded by the fixed strict decoder
`decodeInst` (Sheng–Xiao, arXiv:2609.06512, held version sha256 aca9c70e…, Section 3.1, p.6: a
kernel "maps an instance (I, k) to an instance (I′, k′)"). `none` when the output is not the code
of an instance. -/
def outputOf (mem : ℕ → ℕ) : Option HSInstance :=
  decodeInst (outputList mem)

end HSElemKernel


