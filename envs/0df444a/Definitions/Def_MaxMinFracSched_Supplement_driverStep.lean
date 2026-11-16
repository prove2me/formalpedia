-- Prove2me | Definitions.Def_MaxMinFracSched_Supplement_driverStep
-- name    : MaxMinFracSched_Supplement_driverStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:22:15.465483+00:00
-- url     : https://prove2.me/theorems/6ab79868-9f29-4cfa-bac8-c2f001b21f63
-- title:
--   One operation of an event-driven scheduler
-- statement:
--   Fix a program $P$, an encoding $\mathrm{enc}(j)$ of each job as a list of reals, the parameter $\alpha'$ and a presentation $L$ of the instance. The output of every operation is read as $[\sigma,e,\tau]$: $\sigma$ is the index of the job to serve from now on (any value that is not a job index means idle), and $e>0$ announces an internal event at time $\tau$. One driver step does the following.
--
--   1. If an event is announced and its time $\tau$ is earlier than the arrival time of the next batch, or no batch is left, it runs the operation with input $[1,\tau]$ (advance) at time $\tau$.
--   2. Otherwise, if a batch $j_1,\dots,j_k$ with arrival time $a$ is left, it runs the operation with input $[0,a,\alpha']$ followed by $\mathrm{enc}(j_1),\dots,\mathrm{enc}(j_k)$ (arrival) at time $a$.
--   3. Otherwise the run is finished.
--
--   Each operation runs $P$ from the state the previous one left. The step records the decision (from the operation's time on, serve the job of index $\sigma$, or idle) and the cost. A finished or failed state does not change.
--
--   This is the event loop of Section 8.1.7: "Besides arrivals, an event occurs when a job reaches its target or when a deadline passes."
--
--   **Formalization Note** The driver is fixed and only the program varies. An event announced for the same time as an arrival is processed after the arrival; the program can announce it again.
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 8.1.7, Scheduling bookkeeping, pp.50–51 (PDF pp.52–53); Section 8.1.8, p.51 (PDF p.53)

import Mathlib
import Definitions.Def_BlottoFPTAS_Main_RealRAM
import Definitions.Def_MaxMinFracSched_Job
import Definitions.Def_MaxMinFracSched_Supplement_runOp
import Definitions.Def_MaxMinFracSched_Supplement_batches
import Definitions.Def_MaxMinFracSched_Supplement_DriverState

namespace MaxMinFracSched

namespace Supplement

open BlottoFPTAS.Main.RealRAM

open Classical in
/-- **One operation of an event-driven scheduler.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 8.1.7, "Scheduling bookkeeping", pp.50–51 (PDF pp.52–53): "Between scheduling events,
only the running job's work completion changes … New jobs are inserted on arrival, and jobs with
di ≤ t are detached when their deadlines pass. Besides arrivals, an event occurs when a job reaches
its target or when a deadline passes"; Section 8.1.8, p.51 (PDF p.53).

The instance is presented as the list `L`, in batches `batches L`; each job is encoded by the reals
`enc j`; `α'` is the input parameter. The output of every operation is read as `[σ, e, τ]`:
`σ` is the index of the served job in `(batches L).flatten` (any value that is not such an index
means idle), `e > 0` announces an internal event at time `τ`. One driver step:
1. if an event is announced and its time `τ` is earlier than the next batch's arrival time (or no
   batch is left), run the operation `[1, τ]` (advance) at time `τ`;
2. otherwise, if a batch `B` with arrival time `a` is left, run the operation
   `[0, a, α'] ++ enc j₁ ++ … ++ enc j_k` (arrival) at time `a`;
3. otherwise the run is finished.
Each operation runs the program from the state the previous one left (`runOp`) and appends the new
decision (from the operation's time on, serve the job of index `σ`, or idle) and its cost. A
finished or failed state does not change.

**Formalization Note.** The driver is fixed; only the program is chosen. An internal event at the
same time as an arrival is processed after the arrival (the program announces it again if it is
still due). The machine is told the time of every operation. -/
noncomputable def driverStep (P : Program) (enc : Job → List ℝ) (α' : ℝ) (L : List Job)
    (σ : DriverState) : DriverState :=
  if σ.finished || σ.failed then σ else
    let bs := batches L
    let order := bs.flatten
    let τ := σ.out.getD 2 0
    let arr : Option ℝ := (bs[σ.nextBatch]?).bind (fun B => B.head?.map Job.a)
    let op : Option (ℝ × List ℝ × ℕ × ℕ) :=
      if 0 < σ.out.getD 1 0 ∧ (∀ A, arr = some A → τ < A) then
        some (τ, [1, τ], 0, σ.nextBatch)
      else
        match bs[σ.nextBatch]? with
        | some B => some ((B.head?.map Job.a).getD 0,
            [0, (B.head?.map Job.a).getD 0, α'] ++ B.flatMap enc, B.length, σ.nextBatch + 1)
        | none => none
    match op with
    | none => { σ with finished := true }
    | some (t', xs, k, nb) =>
      match runOp P σ.mach xs with
      | none => { σ with failed := true }
      | some (s', steps, _) =>
        let o := outputOf s'
        let v := o.getD 0 (-1)
        let served : Option Job :=
          if 0 ≤ v ∧ ((⌊v⌋₊ : ℕ) : ℝ) = v then order[⌊v⌋₊]? else none
        ⟨s', t', nb, o, σ.segs ++ [(t', served)], σ.ops ++ [(k, steps)], false, false⟩

end Supplement

end MaxMinFracSched


