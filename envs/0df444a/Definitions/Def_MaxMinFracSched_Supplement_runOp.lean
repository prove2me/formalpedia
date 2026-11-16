-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_runOp
-- name    : MaxMinFracSched_Supplement_runOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:18:45.043004+00:00
-- url     : https://prove2.me/theorems/fd79c2b5-ccd3-49a0-8f3f-4927ca607a5e
-- title:
--   One operation of a persistent real-RAM machine
-- statement:
--   One **operation** runs a deterministic real-RAM program $P$ from the resumed state (previous state $s$, new input $x$) until it first halts. If the run halts after $k$ steps, the outcome consists of:
--
--   1. the halted state $s'$,
--   2. the number $k$ of executed instructions, each of unit cost (the final `halt` included),
--   3. the set of memory cells written during those $k$ steps.
--
--   If the run never halts, there is no outcome. The operation's output is read from the halted state in the machine's output layout (memory cells $-1,\dots,-\ell$, where $\ell$ is the value of pointer register $0$).
--
--   **Formalization Note** The program runs on the all-zero random tape, which a deterministic program never reads.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8, p.40 (PDF p.42); Theorem 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Supplement_resume
import Definitions.Def_MaxMinFracSched_Supplement_storeAddr

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

open Classical in
/-- **One operation of a persistent real-RAM machine.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8, p.40 (PDF p.42): "arithmetic operations, comparisons, assignments, and memory
accesses take O(1) time"; Theorem 8.1.

Run the deterministic program `P` (on the all-zero tape, which a deterministic program never
reads) from `resume s xs` until its first halted state. If it halts after `k` steps, the result is
`some (s', k, W)`: the halted state `s'`, the number `k` of executed instructions (each costs `1`,
the final `halt` included), and the set `W` of memory cells written by those `k` instructions. If it
never halts, the result is `none`. The operation's output is `outputOf s'` (memory cells
`-1, …, -ℓ` with `ℓ` the value of pointer register `0`). -/
noncomputable def runOp (P : Program) (s : State) (xs : List ℝ) : Option (State × ℕ × Finset ℤ) :=
  if h : ∃ k : ℕ, ((step P zeroTape)^[k] (resume s xs)).halted = true then
    some ((step P zeroTape)^[Nat.find h] (resume s xs), Nat.find h,
      (Finset.range (Nat.find h)).biUnion
        (fun i => (storeAddr P ((step P zeroTape)^[i] (resume s xs))).toFinset))
  else none

end Supplement

end MaxMinFracSched


