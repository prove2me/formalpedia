-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveScheduler
-- name    : IntMul_EndParkRecursiveScheduler
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T03:53:02.336687+00:00
-- url     : https://prove2.me/theorems/7803beb5-f5e1-4567-93dc-385c063ea247
-- title:
--   One fixed recursive scheduler with result-only parent restoration
-- source:
--   Original complete fixed recursive scheduler with result-only physical parent restoration. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveScheduler
import Definitions.Def_IntMul_EndParkResume

namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

abbrev State := FlatRecursiveScheduler.State

/-- The two physical restoration controls have the same finite shape. -/
def restoreControl : TrackedSelectiveParentRestore.State → TrackedParentRestore.State
  | .rewind => .rewind
  | .halt => .halt

/-- The complete original scheduler, with only its restoration transition
replaced by the actual result-tape-only service. -/
noncomputable def transition (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (a : Fin (M.k+3) → Sym M) : State M n × (Fin (M.k+3) → Sym M × Move) := by
  classical
  exact if q=.restore .rewind then
    let r := (EndParkResume.restoreMachine M).δ .rewind a
    (.restore (restoreControl r.1),r.2)
  else FlatRecursiveScheduler.transition M n request resume q a

noncomputable abbrev machine (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M n
  qStart := .boot .start
  qHalt := .halt
  start_ne_halt := by simp
  k := M.k+3
  two_le_k := by omega
  δ := transition M n request resume
  start_preserved := by
    classical
    intro q a i hi
    by_cases h : q=.restore .rewind
    · simpa only [transition,if_pos h] using (EndParkResume.restoreMachine M).start_preserved .rewind a i hi
    · simpa only [transition,if_neg h] using
        (FlatRecursiveScheduler.machine M n request resume).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    by_cases h : q=.restore .rewind
    · simpa only [transition,if_pos h] using (EndParkResume.restoreMachine M).start_only_at_start .rewind a i hi
    · simpa only [transition,if_neg h] using
        (FlatRecursiveScheduler.machine M n request resume).start_only_at_start q a i hi
  halt_fixed := by
    intro a
    simp only [transition,reduceCtorEq,if_false]
    rfl
  input_readonly := by
    classical
    intro q a
    by_cases h : q=.restore .rewind
    · simpa only [transition,if_pos h] using (EndParkResume.restoreMachine M).input_readonly .rewind a
    · simpa only [transition,if_neg h] using
        (FlatRecursiveScheduler.machine M n request resume).input_readonly q a

/-- Compile the physical return service into the SAME complete recursive
scheduler. A recovered label enters its actual body continuation directly. -/
def resumeControl (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K) :
    EndParkResume.State n → State M n
  | .restore s => .restore (restoreControl s)
  | .pop s => .pop s
  | .output label s => .output label s
  | .ready label => .body (resume label)
  | .halt => .error

noncomputable def liftResume (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (EndParkResume.machine M n).Cfg) : (machine M n request resume).Cfg where
  state := resumeControl M n resume c.state
  cells := c.cells
  head := c.head

noncomputable def initialFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  liftResume M n request resume (EndParkResume.initialFrame M n base rho sigma offset extent c label w)

noncomputable def finalFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkResume.machine M n).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  liftResume M n request resume (EndParkResume.finalFrame M n base rho sigma offset extent c label w)

end IntMul.EndParkRecursiveScheduler


