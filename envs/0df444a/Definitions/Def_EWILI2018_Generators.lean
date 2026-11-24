-- Prove2me | Definitions.Def_EWILI2018_Generators
-- name    : EWILI2018_Generators
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-24T07:57:47.281742+00:00
-- url     : https://prove2.me/theorems/f4d499c0-cd47-4d5f-babf-7e44fd5f862c
-- title:
--   Table 1 kernel event alphabet and Figure 3 plant generators
-- statement:
--   Defines the $15$-element kernel tracepoint alphabet $\Sigma_{\mathrm{ker}}$ (`KernelEvent`) from Table 1 of EWILI 2018 together with the three deterministic partial plant generators shown in Figure 3 and their partial alphabet projections from $\Sigma_{\mathrm{ker}}$:
--
--   1. **Need Resched (`needReschedGen`)**: $1$-state generator ($\{\mathsf{needResched}\}$, initial and marked) accepting `schedNeedResched` via a self-loop.
--   2. **Sleepable and Runnable (`sleepRunGen`)**: $2$-state generator ($\{\mathsf{sleepable}, \mathsf{runnable}\}$, initial and sole marked state $\mathsf{sleepable}$) transitioning to $\mathsf{runnable}$ on `schedWaking` or `schedSetStateRunnable` and returning to $\mathsf{sleepable}$ on `schedSetStateSleepable`.
--   3. **Scheduling Context (`schedContextGen`)**: $2$-state generator ($\{\mathsf{threadContext}, \mathsf{schedulingContext}\}$, initial and sole marked state $\mathsf{threadContext}$) alternating `scheduleEntry` and `scheduleExit`.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, Modeling the Behavior of Threads in the PREEMPT_RT Linux Kernel Using Automata, §§4.1–4.2, Table 1 and Fig. 3, p. 4. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=4

import Definitions.Def_RamadgeWonham_Shared_Generator
import Definitions.Def_CassandrasLafortune_Parallel

/-! Modeled kernel trace events (Table 1) and component plant generators (Figure 3)
from de Oliveira, Cucinotta, and de Oliveira, *Modeling the Behavior of Threads in the
PREEMPT_RT Linux Kernel Using Automata* (EWILI 2018), §§4.1–4.2, p. 4. -/

namespace EWILI2018

open RamadgeWonham.Shared

/-- Table 1 (p. 4): all fifteen automaton events extracted from kernel tracepoints. -/
inductive KernelEvent where
  | localIrqDisable
  | localIrqEnable
  | preemptDisable
  | preemptEnable
  | schedNeedResched
  | schedSetStateRunnable
  | schedSetStateSleepable
  | scheduleEntry
  | scheduleExit
  | schedSwitchIn
  | schedSwitchInO
  | schedSwitchOutO
  | schedSwitchPreempt
  | schedSwitchSuspend
  | schedWaking
  deriving DecidableEq

/-- Alphabet of the Need Resched generator (Figure 3, top left). -/
inductive NeedReschedEvent where
  | schedNeedResched
  deriving DecidableEq

/-- State of the Need Resched generator (Figure 3, top left). -/
inductive NeedReschedState where
  | needResched
  deriving DecidableEq

/-- Figure 3 (top left): single-state generator accepting `sched_need_resched` at any point. -/
def needReschedGen : Generator NeedReschedEvent where
  Q := NeedReschedState
  q0 := .needResched
  Qm := {.needResched}
  δ _ _ := some .needResched

def needReschedView : KernelEvent → Option NeedReschedEvent
  | .schedNeedResched => some .schedNeedResched
  | _ => none

/-- Alphabet of the Sleepable and Runnable generator (Figure 3, top right). -/
inductive SleepRunEvent where
  | schedWaking
  | schedSetStateRunnable
  | schedSetStateSleepable
  deriving DecidableEq

/-- States of the Sleepable and Runnable generator (Figure 3, top right). -/
inductive SleepRunState where
  | sleepable
  | runnable
  deriving DecidableEq

/-- Figure 3 (top right): initially marked `sleepable`; `sched_waking` and
`sched_set_state_runnable` move to `runnable`, and `sched_set_state_sleepable` returns. -/
def sleepRunGen : Generator SleepRunEvent where
  Q := SleepRunState
  q0 := .sleepable
  Qm := {.sleepable}
  δ e q := match q, e with
    | .sleepable, .schedWaking => some .runnable
    | .sleepable, .schedSetStateRunnable => some .runnable
    | .runnable, .schedSetStateSleepable => some .sleepable
    | _, _ => none

def sleepRunView : KernelEvent → Option SleepRunEvent
  | .schedWaking => some .schedWaking
  | .schedSetStateRunnable => some .schedSetStateRunnable
  | .schedSetStateSleepable => some .schedSetStateSleepable
  | _ => none

/-- Alphabet of the Scheduling Context generator (Figure 3, bottom). -/
inductive SchedContextEvent where
  | scheduleEntry
  | scheduleExit
  deriving DecidableEq

/-- States of the Scheduling Context generator (Figure 3, bottom). -/
inductive SchedContextState where
  | threadContext
  | schedulingContext
  deriving DecidableEq

/-- Figure 3 (bottom): call and return of `__schedule()`, starting and marked in `thread_context`. -/
def schedContextGen : Generator SchedContextEvent where
  Q := SchedContextState
  q0 := .threadContext
  Qm := {.threadContext}
  δ e q := match q, e with
    | .threadContext, .scheduleEntry => some .schedulingContext
    | .schedulingContext, .scheduleExit => some .threadContext
    | _, _ => none

def schedContextView : KernelEvent → Option SchedContextEvent
  | .scheduleEntry => some .scheduleEntry
  | .scheduleExit => some .scheduleExit
  | _ => none

end EWILI2018


