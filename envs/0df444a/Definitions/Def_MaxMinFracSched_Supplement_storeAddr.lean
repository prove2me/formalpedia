-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_storeAddr
-- name    : MaxMinFracSched_Supplement_storeAddr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:18:10.528987+00:00
-- url     : https://prove2.me/theorems/b9941454-832a-49ff-b363-cdb9d5dea168
-- title:
--   Memory cell written by the next real-RAM instruction
-- statement:
--   For a program $P$ and a state $s$, this is the address of the memory cell written by the next step of $P$ from $s$, namely the target cell $M[p_q]$ of a `store` instruction. There is no address when the next step writes no memory cell or when $s$ is halted.
--
--   The **space** of a run is the number of distinct memory cells written in this way (Theorem 8.1).
--
--   **Formalization Note** Registers and pointer registers are indexed by constants of the program, so a fixed program uses $O(1)$ of them; only the memory is unbounded. Input cells are written by the environment and do not count.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **The memory cell written by the next instruction.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42): "can be maintained exactly in O(n log3 n) total time and
O(n log2 n) space".

`storeAddr P s` is the address of the memory cell that the next step of `P` from `s` writes (the
target `M[p[q]]` of a `store` instruction), and `none` when that step writes no memory cell or `s` is
halted. The space of a run is the number of distinct cells written this way.

**Formalization Note.** Only the real memory `ℤ → ℝ` is unbounded; registers and pointer
registers are indexed by constants of the program, so a fixed program uses `O(1)` of them. The
cells of the input area are written by the environment, not by the program. -/
def storeAddr (P : Program) (s : State) : Option ℤ :=
  if s.halted then none else
    match P[s.core.pc]? with
    | some (.core (.store q _)) => some (s.core.ptrs q)
    | _ => none

end Supplement

end MaxMinFracSched


