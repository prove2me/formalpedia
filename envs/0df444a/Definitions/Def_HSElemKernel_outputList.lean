-- Prove2me | Definitions.Def_HSElemKernel_outputList
-- name    : HSElemKernel_outputList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:22:53.912533+00:00
-- url     : https://prove2.me/theorems/a8ace7a6-a06d-4fb5-8dc9-dd4c947b7572
-- title:
--   Output list of a RAM program
-- statement:
--   The **output** of a RAM program is read from its final memory: cell $0$ holds the output length $\ell$ and cells $1, \dots, \ell$ the output entries, a list of natural numbers.
--
--   This fixes where every algorithm of the mission writes its output; fixed decoders (`outputOf`, `decodeCNF`, `decodeHash`) then interpret the list.
--
--   **Formalization Note** The paper names no machine; this is the convention of the mission on the published RAM `TimeSpaceMA_RAM`.
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Section 3.1, p.6 (output of a kernel)

import Mathlib

namespace HSElemKernel

/-- The output list written by a RAM program in its memory `mem` (Sheng–Xiao, arXiv:2609.06512,
held version sha256 aca9c70e…; the paper names no machine): cell `0` holds the length `ℓ` of the
output, and cells `1, …, ℓ` hold its entries.

**Formalization Note** This fixes where every algorithm of the mission writes its output; the
output is then read by a fixed decoder (`outputOf`, `decodeCNF`, `decodeHash`). -/
def outputList (mem : ℕ → ℕ) : List ℕ :=
  (List.range (mem 0)).map (fun i => mem (i + 1))

end HSElemKernel


