-- Prove2me | Definitions.Def_IntMul_FlatRecursiveScheduler
-- name    : IntMul_FlatRecursiveScheduler
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T01:47:30.395776+00:00
-- url     : https://prove2.me/theorems/dac472fd-465c-4073-b2f3-cc73f6864b6e
-- title:
--   One fixed-tape finite recursive scheduler with physical continuation records
-- statement:
--   For any fixed finite multitape body M and finite request/resume labels, this is one deterministic finite scheduler table on exactly M.k+3 tapes and one fixed tagged alphabet. The same body control M.K is used at every recursive depth. Requests physically transfer arguments, push a finite continuation, reserve fresh work banks and prepare a new body invocation. Returns physically replace the shared result buffer, clean the current banks, inspect the continuation tape, restore and pop a parent record, and place the result into the parent output bank. Root input and output use actual copying and output-shift services. The buffer reset and every phase dispatch are actual transitions. Addresses, lengths, call trees and depth appear only in proof frames and never enter the table. This definition provides the finite machine; startup, execution and recursive correctness are separate theorems.
-- source:
--   Original fixed-tape recursive scheduler for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedRootInputCopy
import Definitions.Def_IntMul_TrackedChildInputBridge
import Definitions.Def_IntMul_TrackedBankReservation
import Definitions.Def_IntMul_TrackedReturnReplacement
import Definitions.Def_IntMul_TrackedParentRestore
import Definitions.Def_IntMul_TrackedParentOutputBridge
import Definitions.Def_IntMul_TrackedOutputShift
import Definitions.Def_IntMul_FiniteContinuationStack
import Definitions.Def_IntMul_FixedTapeExtension

namespace IntMul.FlatRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

/-- One fixed finite set of scheduler phases. Call depth is stored physically
on the continuation tape and never appears in this control type. -/
inductive State (M : MultitapeTM) (n : ℕ)
  | boot (s : TrackedRootInputCopy.State)
  | preparation (s : TrackedBankPreparation.State)
  | resetBuffer
  | body (q : M.K)
  | input (q : Fin n) (s : TrackedChildInputBridge.State)
  | push (s : FiniteContinuationStack.State n)
  | reservation (s : TrackedBankReservation.State)
  | returning (s : TrackedReturnReplacement.State)
  | cleanup (s : TrackedBankCleanup.State)
  | inspectStack
  | restore (s : TrackedParentRestore.State)
  | pop (s : FiniteContinuationStack.State n)
  | output (q : Fin n) (s : TrackedParentOutputBridge.State)
  | finish (s : TrackedOutputShift.State)
  | error
  | halt

noncomputable instance (M : MultitapeTM) (n : ℕ) : Fintype (State M n) := by
  classical
  exact {
    elems := (Finset.univ.image State.boot) ∪ (Finset.univ.image State.preparation) ∪
      (Finset.univ.image State.body) ∪
      (Finset.univ.image (fun qs : Fin n × TrackedChildInputBridge.State => State.input qs.1 qs.2)) ∪
      (Finset.univ.image State.push) ∪ (Finset.univ.image State.reservation) ∪
      (Finset.univ.image State.returning) ∪ (Finset.univ.image State.cleanup) ∪
      (Finset.univ.image State.restore) ∪ (Finset.univ.image State.pop) ∪
      (Finset.univ.image (fun qs : Fin n × TrackedParentOutputBridge.State => State.output qs.1 qs.2)) ∪
      (Finset.univ.image State.finish) ∪ {.resetBuffer,.inspectStack,.error,.halt}
    complete := by intro q; cases q <;> simp }

noncomputable abbrev bootMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedRootInputCopy.machine M)
noncomputable abbrev preparationMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedBankPreparation.machine M)
noncomputable abbrev bodyMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedBankedSimulation.machine M)
noncomputable abbrev inputMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedChildInputBridge.machine M)
noncomputable abbrev reservationMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedBankReservation.machine M)
noncomputable abbrev returnMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedReturnReplacement.machine M)
noncomputable abbrev cleanupMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedBankCleanup.machine M)
noncomputable abbrev restoreMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedParentRestore.machine M)
noncomputable abbrev outputMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedParentOutputBridge.machine M)
noncomputable abbrev finishMachine (M : MultitapeTM) := FixedTapeExtension.machine (TrackedOutputShift.machine M)

def bufferTape (M : MultitapeTM) : Fin (M.k+3) := ⟨1,by omega⟩
abbrev stackTape (M : MultitapeTM) := FiniteContinuationStack.stackTape M

noncomputable def moveActions (M : MultitapeTM) (a : Fin (M.k+3) → Sym M)
    (tape : Fin (M.k+3)) (move : Move) : Fin (M.k+3) → Sym M × Move := by
  classical
  exact fun i => TrackedBankCleanup.protect M (a i) (a i) (if i=tape then move else .stay)

noncomputable def transition (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (a : Fin (M.k+3) → Sym M) : State M n × (Fin (M.k+3) → Sym M × Move) := by
  classical
  exact match q with
  | .boot s =>
    if s=(bootMachine M).qHalt then (.preparation .mark,moveActions M a (stackTape M) .right)
    else let r := (bootMachine M).δ s a; (.boot r.1,r.2)
  | .preparation s =>
    if s=(preparationMachine M).qHalt then (.resetBuffer,fun i => (a i,.stay))
    else let r := (preparationMachine M).δ s a; (.preparation r.1,r.2)
  | .resetBuffer =>
    if a (bufferTape M)=some (M.startSym,true) then (.body M.qStart,moveActions M a (bufferTape M) .right)
    else (.resetBuffer,moveActions M a (bufferTape M) .left)
  | .body q =>
    if q=M.qHalt then (.returning (returnMachine M).qStart,fun i => (a i,.stay))
    else match request q with
      | some label => (.input label .before,fun i => (a i,.stay))
      | none => let r := (bodyMachine M).δ q a; (.body r.1,r.2)
  | .input label s =>
    if s=(inputMachine M).qHalt then (.push (.pushStart label),fun i => (a i,.stay))
    else let r := (inputMachine M).δ s a; (.input label r.1,r.2)
  | .push s =>
    if s=.pushDone then (.reservation .seek,fun i => (a i,.stay))
    else let r := FiniteContinuationStack.transition M n s a; (.push r.1,r.2)
  | .reservation s =>
    if s=(reservationMachine M).qHalt then (.preparation .mark,fun i => (a i,.stay))
    else let r := (reservationMachine M).δ s a; (.reservation r.1,r.2)
  | .returning s =>
    if s=(returnMachine M).qHalt then (.cleanup .rewind,fun i => (a i,.stay))
    else let r := (returnMachine M).δ s a; (.returning r.1,r.2)
  | .cleanup s =>
    if s=(cleanupMachine M).qHalt then (.inspectStack,moveActions M a (stackTape M) .left)
    else let r := (cleanupMachine M).δ s a; (.cleanup r.1,r.2)
  | .inspectStack =>
    if a (stackTape M)=none then (.finish .rewind,fun i => (a i,.stay))
    else (.restore .rewind,moveActions M a (stackTape M) .right)
  | .restore s =>
    if s=(restoreMachine M).qHalt then (.pop .popStart,fun i => (a i,.stay))
    else let r := (restoreMachine M).δ s a; (.restore r.1,r.2)
  | .pop s =>
    match s with
    | .resume label => (.output label .before,fun i => (a i,.stay))
    | _ => let r := FiniteContinuationStack.transition M n s a; (.pop r.1,r.2)
  | .output label s =>
    if s=(outputMachine M).qHalt then (.body (resume label),fun i => (a i,.stay))
    else let r := (outputMachine M).δ s a; (.output label r.1,r.2)
  | .finish s =>
    if s=(finishMachine M).qHalt then (.halt,fun i => (a i,.stay))
    else let r := (finishMachine M).δ s a; (.finish r.1,r.2)
  | .error => (.error,fun i => (a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

private theorem transition_actions (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (a : Fin (M.k+3) → Sym M)
    (P : (Fin (M.k+3) → Sym M × Move) → Prop)
    (stay : P (fun i => (a i,.stay)))
    (moves : ∀ tape move, P (moveActions M a tape move))
    (bootP : ∀ s, P ((bootMachine M).δ s a).2)
    (preparationP : ∀ s, P ((preparationMachine M).δ s a).2)
    (bodyP : ∀ s, P ((bodyMachine M).δ s a).2)
    (inputP : ∀ s, P ((inputMachine M).δ s a).2)
    (reservationP : ∀ s, P ((reservationMachine M).δ s a).2)
    (returnP : ∀ s, P ((returnMachine M).δ s a).2)
    (cleanupP : ∀ s, P ((cleanupMachine M).δ s a).2)
    (restoreP : ∀ s, P ((restoreMachine M).δ s a).2)
    (outputP : ∀ s, P ((outputMachine M).δ s a).2)
    (finishP : ∀ s, P ((finishMachine M).δ s a).2)
    (stackP : ∀ s, P (FiniteContinuationStack.transition M n s a).2) (q : State M n) :
    P (transition M n request resume q a).2 := by
  classical
  cases q with
  | boot s =>
    by_cases h : s=(bootMachine M).qHalt
    · simpa only [transition,if_pos h] using moves _ _
    · simpa only [transition,if_neg h] using bootP s
  | preparation s =>
    by_cases h : s=(preparationMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using preparationP s
  | input label s =>
    by_cases h : s=(inputMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using inputP s
  | reservation s =>
    by_cases h : s=(reservationMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using reservationP s
  | returning s =>
    by_cases h : s=(returnMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using returnP s
  | cleanup s =>
    by_cases h : s=(cleanupMachine M).qHalt
    · simpa only [transition,if_pos h] using moves _ _
    · simpa only [transition,if_neg h] using cleanupP s
  | restore s =>
    by_cases h : s=(restoreMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using restoreP s
  | output label s =>
    by_cases h : s=(outputMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using outputP s
  | finish s =>
    by_cases h : s=(finishMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using finishP s
  | resetBuffer =>
    by_cases h : a (bufferTape M)=some (M.startSym,true)
    · simpa only [transition,if_pos h] using moves (bufferTape M) .right
    · simpa only [transition,if_neg h] using moves (bufferTape M) .left
  | body q =>
    by_cases h : q=M.qHalt
    · simpa only [transition,if_pos h] using stay
    · cases hr : request q with
      | some label => simpa only [transition,if_neg h,hr] using stay
      | none => simpa only [transition,if_neg h,hr] using bodyP q
  | push s =>
    by_cases h : s=.pushDone
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using stackP s
  | inspectStack =>
    by_cases h : a (stackTape M)=none
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using moves (stackTape M) .right
  | pop s =>
    cases s <;> simp only [transition]
    all_goals first | exact stay | exact stackP _
  | error => simpa only [transition] using stay
  | halt => simpa only [transition] using stay

private theorem protected_same (M : MultitapeTM) (s : Sym M) (move : Move) :
    (TrackedBankCleanup.protect M s s move).1=s := by cases s <;> rfl

/-- One flat recursive control table. The same finite body control, alphabet
and k+3 tapes are used at every depth. All request, stack, reservation,
preparation, return, cleanup, inspection, restoration and resumption phases
are physical transitions. Recursive correctness is proved separately. -/
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
    apply transition_actions M n request resume a (fun r => (r i).1=none ∧ (r i).2≠.left)
    · simp [hi]
    · intro tape move
      simp only [moveActions,hi,TrackedBankCleanup.protect]
      split_ifs <;> cases move <;> simp
    · intro s; exact (bootMachine M).start_preserved s a i hi
    · intro s; exact (preparationMachine M).start_preserved s a i hi
    · intro s; exact (bodyMachine M).start_preserved s a i hi
    · intro s; exact (inputMachine M).start_preserved s a i hi
    · intro s; exact (reservationMachine M).start_preserved s a i hi
    · intro s; exact (returnMachine M).start_preserved s a i hi
    · intro s; exact (cleanupMachine M).start_preserved s a i hi
    · intro s; exact (restoreMachine M).start_preserved s a i hi
    · intro s; exact (outputMachine M).start_preserved s a i hi
    · intro s; exact (finishMachine M).start_preserved s a i hi
    · intro s; exact (FiniteContinuationStack.machine M n).start_preserved s a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    apply transition_actions M n request resume a (fun r => (r i).1≠none)
    · exact hi
    · intro tape move
      cases h : a i with
      | none => exact False.elim (hi h)
      | some s => simp [moveActions,h,TrackedBankCleanup.protect]
    · intro s; exact (bootMachine M).start_only_at_start s a i hi
    · intro s; exact (preparationMachine M).start_only_at_start s a i hi
    · intro s; exact (bodyMachine M).start_only_at_start s a i hi
    · intro s; exact (inputMachine M).start_only_at_start s a i hi
    · intro s; exact (reservationMachine M).start_only_at_start s a i hi
    · intro s; exact (returnMachine M).start_only_at_start s a i hi
    · intro s; exact (cleanupMachine M).start_only_at_start s a i hi
    · intro s; exact (restoreMachine M).start_only_at_start s a i hi
    · intro s; exact (outputMachine M).start_only_at_start s a i hi
    · intro s; exact (finishMachine M).start_only_at_start s a i hi
    · intro s; exact (FiniteContinuationStack.machine M n).start_only_at_start s a i hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    classical
    intro q a
    apply transition_actions M n request resume a (fun r => (r ⟨0,by omega⟩).1=a ⟨0,by omega⟩)
    · rfl
    · intro tape move
      exact protected_same M (a ⟨0,by omega⟩) _
    · intro s; exact (bootMachine M).input_readonly s a
    · intro s; exact (preparationMachine M).input_readonly s a
    · intro s; exact (bodyMachine M).input_readonly s a
    · intro s; exact (inputMachine M).input_readonly s a
    · intro s; exact (reservationMachine M).input_readonly s a
    · intro s; exact (returnMachine M).input_readonly s a
    · intro s; exact (cleanupMachine M).input_readonly s a
    · intro s; exact (restoreMachine M).input_readonly s a
    · intro s; exact (outputMachine M).input_readonly s a
    · intro s; exact (finishMachine M).input_readonly s a
    · intro s; exact (FiniteContinuationStack.machine M n).input_readonly s a

noncomputable def liftBoot (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bootMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .boot c.state
  cells := c.cells
  head := c.head

noncomputable def liftPreparation (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (preparationMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .preparation c.state
  cells := c.cells
  head := c.head

noncomputable def liftBody (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (bodyMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .body c.state
  cells := c.cells
  head := c.head

noncomputable def liftInput (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (inputMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .input label c.state
  cells := c.cells
  head := c.head

noncomputable def liftReservation (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (reservationMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .reservation c.state
  cells := c.cells
  head := c.head

noncomputable def liftReturn (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (returnMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .returning c.state
  cells := c.cells
  head := c.head

noncomputable def liftCleanup (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (cleanupMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .cleanup c.state
  cells := c.cells
  head := c.head

noncomputable def liftRestore (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (restoreMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .restore c.state
  cells := c.cells
  head := c.head

noncomputable def liftOutput (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (c : (outputMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .output label c.state
  cells := c.cells
  head := c.head

noncomputable def liftFinish (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (finishMachine M).Cfg) : (machine M n request resume).Cfg where
  state := .finish c.state
  cells := c.cells
  head := c.head

noncomputable def liftPush (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) : (machine M n request resume).Cfg where
  state := .push c.state
  cells := c.cells
  head := c.head

noncomputable def liftPop (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (c : (FiniteContinuationStack.machine M n).Cfg) : (machine M n request resume).Cfg where
  state := .pop c.state
  cells := c.cells
  head := c.head

noncomputable def relabel (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (c : (machine M n request resume).Cfg) : (machine M n request resume).Cfg where
  state := q
  cells := c.cells
  head := c.head

noncomputable def headFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (q : State M n) (c : (machine M n request resume).Cfg) (tape : Fin (M.k+3)) (pos : ℕ) :
    (machine M n request resume).Cfg where
  state := q
  cells := c.cells
  head := Function.update c.head tape pos

noncomputable def parentBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (sigma : ℕ) (v : List Bool) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i.val=1 then TrackedOutputReturn.bufferTape M
    (base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)) sigma v
    else base.cells (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)
  head := fun i => if i.val=1 then sigma+v.length+1
    else base.head (FixedTapeExtension.oldTape (TrackedBankedSimulation.machine M) i)

noncomputable def stackBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho : ℕ) : (bodyMachine M).Cfg where
  state := M.qStart
  cells := fun i => if i=stackTape M then FiniteContinuationStack.freshTape M (base.cells i) rho else base.cells i
  head := fun i => if i=stackTape M then rho else base.head i

/-- A normal physical body frame, with arbitrary ancestor prefixes, an
actual older shared return word, fixed local banks, and a fresh stack suffix.
All address and word data here are proof parameters, never delta inputs. -/
noncomputable def bodyFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (machine M n request resume).Cfg :=
  liftBody M n request resume (FixedTapeExtension.embed (TrackedBankedSimulation.machine M)
    (stackBase M n request resume base rho)
    (TrackedBankedSimulation.embed M (parentBase M n request resume base sigma v) offset extent c))

noncomputable def nativeBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    (machine M n request resume).Cfg where
  state := .body M.qStart
  cells := ((machine M n request resume).initCfg x y).cells
  head := fun i => if i.val=0 then (TrackedBankPreparation.inputWord M x y).length+1 else 0

noncomputable def nativeFinalFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y w : List Bool) :
    (machine M n request resume).Cfg where
  state := .halt
  cells := fun i => if i.val=1 then TrackedOutputShift.outputTape M
    (((machine M n request resume).initCfg x y).cells i) w
    else ((machine M n request resume).initCfg x y).cells i
  head := fun i => if i.val=0 then (TrackedBankPreparation.inputWord M x y).length+1
    else if i.val=1 then w.length+1 else if i=stackTape M then 0 else 1

end IntMul.FlatRecursiveScheduler


