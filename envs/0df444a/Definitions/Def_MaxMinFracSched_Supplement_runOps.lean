-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_runOps
-- name    : MaxMinFracSched_Supplement_runOps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:19:21.933198+00:00
-- url     : https://prove2.me/theorems/835e0380-246b-48ae-a008-4a811f604bc0
-- title:
--   A sequence of operations on a persistent real-RAM machine
-- statement:
--   Given a program $P$, an initial state $s$ and the inputs $x_1,\dots,x_m$ of $m$ operations, the operations are run one after the other, each from the state the previous one left. If every operation halts, the result is the list of the $m$ outcomes (output, number of executed instructions, cells written), in order; if some operation never halts, there is no result.
--
--   Theorem 8.1 runs the batches of arriving jobs in this way.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Supplement_runOp

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

/-- **A sequence of operations on a persistent real-RAM machine.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Theorem 8.1, p.40 (PDF p.42): "Over a sequence of n job arrivals … A batch of
k ≥ 1 jobs arriving at a common time is processed in worst-case O(k log3 n) time."

`runOps P s [x₁, …, x_m]` runs the operations with inputs `x₁, …, x_m` one after the other, each from
the state the previous one left (`runOp`), starting from `s`. If every operation halts, the result
is the list of their outcomes `(output, steps, cells written)`, in order; if some operation never
halts, the result is `none`. -/
noncomputable def runOps (P : Program) : State → List (List ℝ) → Option (List (List ℝ × ℕ × Finset ℤ))
  | _, [] => some []
  | s, xs :: rest =>
    match runOp P s xs with
    | none => none
    | some (s', k, W) => (runOps P s' rest).map (fun l => (outputOf s', k, W) :: l)

end Supplement

end MaxMinFracSched


