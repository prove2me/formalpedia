-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_resume
-- name    : MaxMinFracSched_Supplement_resume
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:17:39.314264+00:00
-- url     : https://prove2.me/theorems/567c182a-25f3-433a-8099-af711742c621
-- title:
--   Resuming a persistent real-RAM machine on a new operation
-- statement:
--   A data structure that persists across operations runs one program on each operation, starting from the machine state that the previous operation left. The machine is the published unit-cost real RAM. To resume a state $s$ on an operation with input list $x$:
--
--   1. every register, pointer register and memory cell of $s$ is kept,
--   2. the input is written into the input area in the machine's own layout: memory cell $0$ holds $|x|$ and cells $1,\dots,|x|$ hold $x$,
--   3. the program counter is set to $0$, the halted flag is cleared and the instruction counter is reset.
--
--   This is the arithmetic RAM of Section 8 (p.40), in which arithmetic operations, comparisons, assignments and memory accesses take unit time, used online.
--
--   **Formalization Note** Cells outside the input area keep their values, so a program can keep its data structure there, for example at negative addresses below its output cells. Input cells beyond $|x|$ keep stale values; the length in cell $0$ marks the end of the input.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8, p.40 (PDF p.42); Theorem 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **Resuming a persistent real-RAM machine on a new operation.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8, p.40 (PDF p.42): "we furnish these bounds for the arithmetic RAM model,
meaning that arithmetic operations, comparisons, assignments, and memory accesses take O(1)
time"; Theorem 8.1: "Over a sequence of n job arrivals … can be maintained".

The machine is the published unit-cost real RAM `BlottoFPTAS.Main.RealRAM`. A data structure that
persists across operations is run on each operation from the state its previous operation left:
`resume s xs` keeps all registers, pointers and memory of `s`, writes the operation's input in the
input area exactly as the machine's own input layout does (memory cell `0` holds `|xs|`, cells
`1, …, |xs|` hold `xs`), sets the program counter to `0`, clears the halted flag and resets the
instruction counter.

**Formalization Note.** Every other memory cell keeps its value, so the program can keep its data
structure in cells outside the input area (for example at negative addresses below its output
cells `-1, …, -ℓ`). Cells of the input area beyond `|xs|` keep stale values; the length in cell `0`
tells the program where the input ends. -/
noncomputable def resume (s : State) (xs : List ℝ) : State :=
  { s with
    core := { s.core with
      pc := 0
      mem := fun z => if z = 0 then (xs.length : ℝ)
        else if 0 < z ∧ z ≤ xs.length then xs.getD (z.toNat - 1) 0 else s.core.mem z }
    halted := false
    work := 0 }

end Supplement

end MaxMinFracSched


