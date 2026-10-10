-- Prove2me | Definitions.Def_IntMul_EndParkRecursiveExecution
-- name    : IntMul_EndParkRecursiveExecution
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T04:09:06.162172+00:00
-- url     : https://prove2.me/theorems/2e536690-2104-43ce-ba45-84a755196d2a
-- title:
--   Exact frames and finite evaluations for the selective-return recursive scheduler
-- source:
--   Original exact recursive frame and charged finite evaluation definitions for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveScheduler


namespace IntMul.EndParkRecursiveScheduler

open IntMul.TrackedBankedSimulation (Sym)

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


end IntMul.EndParkRecursiveScheduler


namespace IntMul.EndParkRecursiveReturn

open IntMul.EndParkRecursiveScheduler

/-- Relative work-head positions after physical output-buffer replacement. -/
noncomputable def returnedHeads (M : MultitapeTM) (c : M.Cfg) : Fin M.k → ℕ := by
  classical
  exact fun j => if j=M.outTape then 0 else c.head j

/-- The complete configuration after returning and clearing one invocation,
with the physical stack probe positioned one cell left of its former end.
The ancestor prefixes, shared result and fixed extra tape remain literal. -/
noncomputable def inspectionFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (w : List Bool) : (machine M n request resume).Cfg where
  state := .inspectStack
  cells := fun i => if h : i.val < M.k+2 then
    if hw : 2 ≤ i.val then TrackedBankCleanup.freshTape M (base.cells i)
      (offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw))
    else if i.val=1 then TrackedOutputReturn.bufferTape M (base.cells i) sigma w
    else base.cells i
    else FiniteContinuationStack.freshTape M (base.cells i) rho
  head := fun i => if h : i.val < M.k+2 then
    if hw : 2 ≤ i.val then offset (BankedSimulation.innerTape M ⟨i.val,h⟩ hw)
    else if i.val=1 then sigma+w.length+1 else base.head i
    else rho-1

end IntMul.EndParkRecursiveReturn


namespace IntMul.EndParkRecursiveCall

open IntMul.EndParkRecursiveScheduler

/-- Argument transfer physically rewinds the parent's packet/output head
while retaining its entire logical contents and all other head positions. -/
noncomputable def parentAfterInput (M : MultitapeTM) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun j => if j=M.outTape then 0 else c.head j

/-- The parent's logical result after a child return, with the recovered
finite resume control and every work head physically parked at its marker. -/
noncomputable def parentAfterChild (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (label : Fin n) (c : M.Cfg) (w : List Bool) : M.Cfg where
  state := resume label
  cells := fun j => if j=M.outTape then M.tapeOf (w.map M.bitSym) else c.cells j
  head := fun _ => 0

noncomputable def parentAfterChildExtent (M : MultitapeTM) (extent : Fin M.k → ℕ)
    (w : List Bool) : Fin M.k → ℕ := fun j => if j=M.outTape then w.length else extent j

/-- Saved parent/ancestor prefixes and a physically appended finite label
record. The child boundary on each work tape is its first fresh cell beyond
the parent's visited extent. The shared argument buffer is physically empty. -/
noncomputable def childBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) : (machine M n request resume).Cfg where
  state := .body M.qStart
  cells := fun i => if i=stackTape M then
    FiniteContinuationStack.recordTape M n (base.cells i) rho label n
    else if i.val=1 then TrackedOutputReturn.bufferTape M (base.cells i) sigma []
    else (bodyFrame M n request resume base rho sigma offset extent c []).cells i
  head := fun i => if i=stackTape M then rho+n+1 else if i.val=1 then sigma+1
    else if h : i.val < M.k+2 then
      if hw : 2 ≤ i.val then TrackedBankReservation.newOffsets M offset extent
        (BankedSimulation.innerTape M ⟨i.val,h⟩ hw) else base.head i
    else base.head i

/-- Complete new invocation of the SAME body control on the SAME fixed
physical tapes, preserving the saved parent and continuation record. -/
noncomputable def childFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (x y : List Bool) :
    (machine M n request resume).Cfg :=
  bodyFrame M n request resume (childBase M n request resume base rho sigma offset extent c label)
    (rho+n+1) sigma (TrackedBankReservation.newOffsets M offset extent)
    (TrackedBankPreparation.initialExtent M x y) (M.initCfg x y) []

end IntMul.EndParkRecursiveCall


namespace IntMul.EndParkRecursiveResume

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall

/-- Actual continuation-probe frame after complete child cleanup. -/
noncomputable def childInspection (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  EndParkRecursiveReturn.inspectionFrame M n request resume
    (childBase M n request resume base rho sigma offset extent c label)
    (rho+n+1) sigma (TrackedBankReservation.newOffsets M offset extent) w

/-- Logical parent configuration produced by the optimized physical return. -/
noncomputable def resumedParent (M : MultitapeTM) (n : ℕ) (resume : Fin n → M.K)
    (label : Fin n) (extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : M.Cfg where
  state := resume label
  cells := fun j => if j=M.outTape then M.tapeOf (w.map M.bitSym) else c.cells j
  head := fun j => if j=M.outTape then 0 else extent j+1

/-- Copy a complete scheduler base to the physical return service's type.
This is a proof frame, not an extra machine instruction or runtime oracle. -/
noncomputable def serviceBase (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (EndParkRecursiveScheduler.machine M n request resume).Cfg) :
    (EndParkResume.machine M n).Cfg where
  state := .halt
  cells := base.cells
  head := base.head

/-- Complete resumed parent body, with recovered continuation, canonical
result bank, new output extent, the result head at zero and other work heads at their retained bank ends, and restored stack. -/
noncomputable def resumedFrame (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool) :
    (machine M n request resume).Cfg :=
  bodyFrame M n request resume base rho sigma offset (parentAfterChildExtent M extent w)
    (resumedParent M n resume label extent c w) w

end IntMul.EndParkRecursiveResume


namespace IntMul.EndParkRecursiveEvaluation

open IntMul.EndParkRecursiveScheduler
open IntMul.EndParkRecursiveCall
open IntMul.EndParkRecursiveReturn
open IntMul.EndParkRecursiveResume
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (nextExtent)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

/-- Exact upper bound for the charged physical return and cleanup protocol. -/
noncomputable def returnCost (M : MultitapeTM) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v w : List Bool) : ℕ :=
  max (c.head M.outTape) (v.length+1)+2*max w.length v.length+w.length+
    span M (returnedHeads M c)+2*span M extent+12

/-- Exact upper bound for real argument transfer, stack push, reservation,
preparation, dispatches and shared-buffer reset. -/
noncomputable def callCost (M : MultitapeTM) (n : ℕ) (extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : ℕ :=
  max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
    3*(inputWord M x y).length+
    span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16

/-- Exact upper bound for real result-marker restoration, stack pop and result
placement, including every physical dispatch. -/
noncomputable def resumeCost (M : MultitapeTM) (n : ℕ) (extent : Fin M.k → ℕ) (w : List Bool) : ℕ :=
  extent M.outTape+n+w.length+2*max w.length (extent M.outTape)+13

/-- Finite recursive evaluation of the original body and finite call controls.
Ordinary nodes are actual body transitions. A call evaluates the same body
from native logical child input and then the physically parked parent with
its result bank replaced. The shared word is tracked only to charge costs.
This is a finite proof tree, never data available to the machine's delta. -/
inductive Evaluates (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) :
    (Fin M.k → ℕ) → M.Cfg → List Bool → List Bool → ℕ → Prop
  | halt (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool)
      (halt : c.state=M.qHalt) (out : c.cells M.outTape=M.tapeOf (w.map M.bitSym)) :
      Evaluates M n request resume extent c v w (returnCost M extent c v w)
  | step (extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (budget : ℕ)
      (live : c.state≠M.qHalt) (ordinary : request c.state=none)
      (rest : Evaluates M n request resume (nextExtent M c extent) (M.step c) v w budget) :
      Evaluates M n request resume extent c v w (budget+1)
  | call (extent : Fin M.k → ℕ) (c : M.Cfg) (v x y childWord w : List Bool)
      (label : Fin n) (childBudget parentBudget : ℕ)
      (live : c.state≠M.qHalt) (request_label : request c.state=some label)
      (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
      (child : Evaluates M n request resume (initialExtent M x y) (M.initCfg x y) [] childWord childBudget)
      (parent : Evaluates M n request resume (parentAfterChildExtent M extent childWord)
        (resumedParent M n resume label extent c childWord) childWord w parentBudget) :
      Evaluates M n request resume extent c v w
        (callCost M n extent c v x y+childBudget+resumeCost M n extent childWord+parentBudget)

end IntMul.EndParkRecursiveEvaluation


