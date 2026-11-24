-- Prove2me | Definitions.Def_EWILI2018_SchedulerSpec
-- name    : EWILI2018_SchedulerSpec
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-24T07:58:21.491299+00:00
-- url     : https://prove2.me/theorems/df5f71ec-e053-4a45-9926-12153a996877
-- title:
--   Figure 4 scheduler-call specification, four-automaton product, and Figure 5 trace
-- statement:
--   Defines the $7$-state, $20$-transition scheduler-call specification `schedulerSpec` over its $8$-event alphabet from Figure 4 of EWILI 2018 (initial and sole marked state $\mathsf{notRunning}$), explicit finite enumerations for transition-table compilation, the $28$-state synchronous parallel composition `publishedThreadModel` combining Figure 3's three plant generators with Figure 4's specification over all $15$ Table 1 kernel events, and the $9$-event `kworker/0:2` kernel trace excerpt (`figure5KernelTrace`) alongside the $8$-event sequence (`table2Events`) and $7$ intermediate target states (`table2States`) of Figure 5 and Table 2.
-- source:
--   D. B. de Oliveira, T. Cucinotta and R. S. de Oliveira, EWILI 2018, §§3, 4.2 and 5, Figs. 4–5 and Table 2, pp. 3–5. https://retis.santannapisa.it/~tommaso/publications/EWILI-2018-Automata.pdf#page=5

import Definitions.Def_EWILI2018_Generators
import Definitions.Def_LinuxRV_TransitionTable

/-! Scheduler-call specification (Figure 4), synchronized four-automaton product (§§3, 4.2),
and kernel trace excerpt with Table 2 reference steps (Figure 5, Table 2) from EWILI 2018, pp. 4–5. -/

namespace EWILI2018

open RamadgeWonham.Shared

/-- Eight-event alphabet of the Figure 4 specification. -/
inductive SchedulerSpecEvent where
  | scheduleEntry
  | schedWaking
  | schedNeedResched
  | schedSwitchIn
  | schedSetStateSleepable
  | schedSetStateRunnable
  | schedSwitchPreempt
  | schedSwitchSuspend
  deriving DecidableEq

/-- Seven states of Figure 4 (p. 5); `notRunning` is both the initial and the sole marked state. -/
inductive SchedulerSpecState where
  | notRunning
  | running
  | sleepable
  | preemptionRunnable
  | preemptionSleepable
  | preemptionToRunnable
  | suspending
  deriving DecidableEq

/-- Figure 4 (p. 5): specification of necessary and sufficient conditions to call the scheduler. -/
def schedulerSpec : Generator SchedulerSpecEvent where
  Q := SchedulerSpecState
  q0 := .notRunning
  Qm := {.notRunning}
  δ e q := match q, e with
    | .notRunning, .scheduleEntry => some .notRunning
    | .notRunning, .schedWaking => some .notRunning
    | .notRunning, .schedNeedResched => some .notRunning
    | .notRunning, .schedSwitchIn => some .running
    | .running, .schedSetStateSleepable => some .sleepable
    | .running, .schedNeedResched => some .preemptionRunnable
    | .sleepable, .schedSetStateRunnable => some .running
    | .sleepable, .schedWaking => some .running
    | .sleepable, .schedNeedResched => some .preemptionSleepable
    | .sleepable, .scheduleEntry => some .suspending
    | .preemptionRunnable, .scheduleEntry => some .preemptionRunnable
    | .preemptionRunnable, .schedSwitchPreempt => some .notRunning
    | .preemptionSleepable, .schedSwitchIn => some .sleepable
    | .preemptionSleepable, .scheduleEntry => some .preemptionSleepable
    | .preemptionSleepable, .schedSwitchPreempt => some .preemptionSleepable
    | .preemptionSleepable, .schedWaking => some .preemptionToRunnable
    | .preemptionToRunnable, .scheduleEntry => some .preemptionToRunnable
    | .preemptionToRunnable, .schedSwitchPreempt => some .preemptionToRunnable
    | .preemptionToRunnable, .schedSwitchIn => some .running
    | .suspending, .schedSwitchSuspend => some .notRunning
    | _, _ => none

def schedulerSpecView : KernelEvent → Option SchedulerSpecEvent
  | .scheduleEntry => some .scheduleEntry
  | .schedWaking => some .schedWaking
  | .schedNeedResched => some .schedNeedResched
  | .schedSwitchIn => some .schedSwitchIn
  | .schedSetStateSleepable => some .schedSetStateSleepable
  | .schedSetStateRunnable => some .schedSetStateRunnable
  | .schedSwitchPreempt => some .schedSwitchPreempt
  | .schedSwitchSuspend => some .schedSwitchSuspend
  | _ => none

def schedulerStateEnum : SchedulerSpecState ≃ Fin 7 where
  toFun
    | .notRunning => 0
    | .running => 1
    | .sleepable => 2
    | .preemptionRunnable => 3
    | .preemptionSleepable => 4
    | .preemptionToRunnable => 5
    | .suspending => 6
  invFun
    | ⟨0, _⟩ => .notRunning
    | ⟨1, _⟩ => .running
    | ⟨2, _⟩ => .sleepable
    | ⟨3, _⟩ => .preemptionRunnable
    | ⟨4, _⟩ => .preemptionSleepable
    | ⟨5, _⟩ => .preemptionToRunnable
    | ⟨6, _⟩ => .suspending
  left_inv q := by cases q <;> rfl
  right_inv
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ => rfl

def schedulerEventEnum : SchedulerSpecEvent ≃ Fin 8 where
  toFun
    | .scheduleEntry => 0
    | .schedWaking => 1
    | .schedNeedResched => 2
    | .schedSwitchIn => 3
    | .schedSetStateSleepable => 4
    | .schedSetStateRunnable => 5
    | .schedSwitchPreempt => 6
    | .schedSwitchSuspend => 7
  invFun
    | ⟨0, _⟩ => .scheduleEntry
    | ⟨1, _⟩ => .schedWaking
    | ⟨2, _⟩ => .schedNeedResched
    | ⟨3, _⟩ => .schedSwitchIn
    | ⟨4, _⟩ => .schedSetStateSleepable
    | ⟨5, _⟩ => .schedSetStateRunnable
    | ⟨6, _⟩ => .schedSwitchPreempt
    | ⟨7, _⟩ => .schedSwitchSuspend
  left_inv e := by cases e <;> rfl
  right_inv
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩ => rfl

/-- Joint state of the three Figure 3 generators and the Figure 4 specification. -/
abbrev ThreadModelState :=
  NeedReschedState × SleepRunState × SchedContextState × SchedulerSpecState

/-- Synchronous parallel composition (§§3 and 4.2) of the four automata drawn in Figures 3–4
over the full 15-event Table 1 alphabet. Events outside a component's alphabet leave that
component unchanged; shared events require every participating component to transition. -/
def publishedThreadModel : Generator KernelEvent where
  Q := ThreadModelState
  q0 := (.needResched, .sleepable, .threadContext, .notRunning)
  Qm := {q | q.1 ∈ needReschedGen.Qm ∧ q.2.1 ∈ sleepRunGen.Qm ∧
    q.2.2.1 ∈ schedContextGen.Qm ∧ q.2.2.2 ∈ schedulerSpec.Qm}
  δ e q := do
    let n ← CassandrasLafortune.localStep needReschedGen q.1 (needReschedView e)
    let sr ← CassandrasLafortune.localStep sleepRunGen q.2.1 (sleepRunView e)
    let sc ← CassandrasLafortune.localStep schedContextGen q.2.2.1 (schedContextView e)
    let sp ← CassandrasLafortune.localStep schedulerSpec q.2.2.2 (schedulerSpecView e)
    pure (n, sr, sc, sp)

def kernelEventEnum : KernelEvent ≃ Fin 15 where
  toFun
    | .localIrqDisable => 0
    | .localIrqEnable => 1
    | .preemptDisable => 2
    | .preemptEnable => 3
    | .schedNeedResched => 4
    | .schedSetStateRunnable => 5
    | .schedSetStateSleepable => 6
    | .scheduleEntry => 7
    | .scheduleExit => 8
    | .schedSwitchIn => 9
    | .schedSwitchInO => 10
    | .schedSwitchOutO => 11
    | .schedSwitchPreempt => 12
    | .schedSwitchSuspend => 13
    | .schedWaking => 14
  invFun
    | ⟨0, _⟩ => .localIrqDisable
    | ⟨1, _⟩ => .localIrqEnable
    | ⟨2, _⟩ => .preemptDisable
    | ⟨3, _⟩ => .preemptEnable
    | ⟨4, _⟩ => .schedNeedResched
    | ⟨5, _⟩ => .schedSetStateRunnable
    | ⟨6, _⟩ => .schedSetStateSleepable
    | ⟨7, _⟩ => .scheduleEntry
    | ⟨8, _⟩ => .scheduleExit
    | ⟨9, _⟩ => .schedSwitchIn
    | ⟨10, _⟩ => .schedSwitchInO
    | ⟨11, _⟩ => .schedSwitchOutO
    | ⟨12, _⟩ => .schedSwitchPreempt
    | ⟨13, _⟩ => .schedSwitchSuspend
    | ⟨14, _⟩ => .schedWaking
  left_inv e := by cases e <;> rfl
  right_inv
    | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ | ⟨6, _⟩ | ⟨7, _⟩
    | ⟨8, _⟩ | ⟨9, _⟩ | ⟨10, _⟩ | ⟨11, _⟩ | ⟨12, _⟩ | ⟨13, _⟩ | ⟨14, _⟩ => rfl

def threadModelStateEnum : ThreadModelState ≃ Fin 28 where
  toFun
    | (.needResched, .sleepable, .threadContext, q) =>
        ⟨(schedulerStateEnum q).val, by omega⟩
    | (.needResched, .sleepable, .schedulingContext, q) =>
        ⟨7 + (schedulerStateEnum q).val, by omega⟩
    | (.needResched, .runnable, .threadContext, q) =>
        ⟨14 + (schedulerStateEnum q).val, by omega⟩
    | (.needResched, .runnable, .schedulingContext, q) =>
        ⟨21 + (schedulerStateEnum q).val, by omega⟩
  invFun i :=
    if h1 : i.val < 7 then
      (.needResched, .sleepable, .threadContext, schedulerStateEnum.symm ⟨i.val, h1⟩)
    else if h2 : i.val < 14 then
      (.needResched, .sleepable, .schedulingContext,
        schedulerStateEnum.symm ⟨i.val - 7, by omega⟩)
    else if h3 : i.val < 21 then
      (.needResched, .runnable, .threadContext,
        schedulerStateEnum.symm ⟨i.val - 14, by omega⟩)
    else
      (.needResched, .runnable, .schedulingContext,
        schedulerStateEnum.symm ⟨i.val - 21, by omega⟩)
  left_inv
    | (.needResched, s, c, q) => by
        cases s <;> cases c <;> cases q <;> decide
  right_inv i := by
    dsimp only
    split_ifs with h1 h2 h3 <;>
      simp only [schedulerStateEnum.apply_symm_apply, Fin.ext_iff] <;> omega

/-- Figure 5 (p. 5): the 9-line kernel trace excerpt for `kworker/0:2` (PID 728). -/
def figure5KernelTrace : List KernelEvent :=
  [ .schedSwitchIn
  , .schedSetStateSleepable
  , .schedNeedResched
  , .scheduleEntry
  , .schedSwitchPreempt
  , .schedWaking
  , .schedSwitchIn
  , .scheduleEntry
  , .schedSwitchPreempt ]

/-- Table 2 (p. 5): the 8 specification events corresponding to Lines 1–8 of Figure 5. -/
def table2Events : List SchedulerSpecEvent :=
  [ .schedSwitchIn
  , .schedSetStateSleepable
  , .schedNeedResched
  , .scheduleEntry
  , .schedSwitchPreempt
  , .schedWaking
  , .schedSwitchIn
  , .scheduleEntry ]

/-- Table 2 (p. 5): target states reached after Lines 1–7 before Line 8 is rejected. -/
def table2States : Vector SchedulerSpecState 7 :=
  #v[ .running
    , .sleepable
    , .preemptionSleepable
    , .preemptionSleepable
    , .preemptionSleepable
    , .preemptionToRunnable
    , .running ]

end EWILI2018


