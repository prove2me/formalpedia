-- Prove2me | Definitions.Def_IntMul_TrackedMarshalledCall
-- name    : IntMul_TrackedMarshalledCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T01:06:26.224596+00:00
-- url     : https://prove2.me/theorems/2cad1b15-b059-45ce-8102-db42ad8fef5f
-- title:
--   Fixed-tape physically marshalled child call with saved and recovered finite return control
-- statement:
--   One finite shared-tape table on k+3 fixed tapes and the common tagged alphabet physically copies an existing parent request into the caller buffer, pushes a finite continuation record, reserves and initializes child work banks, executes the fixed child machine, copies its result out, clears all child banks, restores parent heads and the entire continuation stack, and physically places the result into the parent output bank. Three outer phase boundaries are actual charged stay transitions. No word length, address, workspace extent or recursion depth occurs in the transition table. The table returns to the recovered finite resume state rather than the separate designated halt. The parent must already have physically computed the request packet. This is a complete generic one-level service, not the unbounded recursive fast multiplication scheduler.
-- source:
--   Original physically marshalled saved caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedChildInputBridge
import Definitions.Def_IntMul_TrackedParentOutputBridge
import Definitions.Def_IntMul_SavedContinuationCall

namespace IntMul.TrackedMarshalledCall

open IntMul.TrackedBankedSimulation (Sym)

noncomputable abbrev inputMachine (M : MultitapeTM) : MultitapeTM :=
  FixedTapeExtension.machine (TrackedChildInputBridge.machine M)

noncomputable abbrev outputMachine (M : MultitapeTM) : MultitapeTM :=
  FixedTapeExtension.machine (TrackedParentOutputBridge.machine M)

abbrev State (M : MultitapeTM) (n : ℕ) := (Fin n × TrackedChildInputBridge.State) ⊕
  (SavedContinuationCall.State M n ⊕ ((Fin n × TrackedParentOutputBridge.State) ⊕ (Fin n ⊕ Unit)))

def resumeLabel (M : MultitapeTM) (n : ℕ) : SavedContinuationCall.State M n → Option (Fin n)
  | .inr (.inr (.resume q)) => some q
  | _ => none

noncomputable def transition (M : MultitapeTM) (n : ℕ) (q : State M n)
    (a : Fin (M.k+3) → Sym M) : State M n × (Fin (M.k+3) → Sym M × Move) := by
  classical
  exact match q with
  | .inl (q,s) =>
      if s=(inputMachine M).qHalt then (.inr (.inl (.inl (.pushStart q))),fun i => (a i,.stay))
      else let r := (inputMachine M).δ s a; (.inl (q,r.1),r.2)
  | .inr (.inl s) =>
      match resumeLabel M n s with
      | some q => (.inr (.inr (.inl (q,(outputMachine M).qStart))),fun i => (a i,.stay))
      | none => let r := SavedContinuationCall.transition M n s a; (.inr (.inl r.1),r.2)
  | .inr (.inr (.inl (q,s))) =>
      if s=(outputMachine M).qHalt then (.inr (.inr (.inr (.inl q))),fun i => (a i,.stay))
      else let r := (outputMachine M).δ s a; (.inr (.inr (.inl (q,r.1))),r.2)
  | .inr (.inr (.inr s)) => (.inr (.inr (.inr s)),fun i => (a i,.stay))

private theorem transition_actions (M : MultitapeTM) (n : ℕ) (a : Fin (M.k+3) → Sym M)
    (P : (Fin (M.k+3) → Sym M × Move) → Prop)
    (stay : P (fun i => (a i,.stay)))
    (input : ∀ s, P ((inputMachine M).δ s a).2)
    (saved : ∀ s, P (SavedContinuationCall.transition M n s a).2)
    (output : ∀ s, P ((outputMachine M).δ s a).2) (q : State M n) :
    P (transition M n q a).2 := by
  classical
  cases q with
  | inl p =>
    rcases p with ⟨q,s⟩
    by_cases h : s=(inputMachine M).qHalt
    · simpa only [transition,if_pos h] using stay
    · simpa only [transition,if_neg h] using input s
  | inr p =>
    cases p with
    | inl s =>
      cases h : resumeLabel M n s with
      | none => simpa only [transition,h] using saved s
      | some q => simpa only [transition,h] using stay
    | inr p =>
      cases p with
      | inl p =>
        rcases p with ⟨q,s⟩
        by_cases h : s=(outputMachine M).qHalt
        · simpa only [transition,if_pos h] using stay
        · simpa only [transition,if_neg h] using output s
      | inr s => simpa only [transition] using stay

/-- One finite shared-tape service physically marshals parent arguments,
saves return control, calls the child, restores the stack and parent banks,
and physically delivers the returned result into the parent output bank.
Every phase boundary costs one actual transition. -/
noncomputable abbrev machine (M : MultitapeTM) (n : ℕ) (initial : Fin n) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State M n
  qStart := .inl (initial,.before)
  qHalt := .inr (.inr (.inr (.inr ())))
  start_ne_halt := by simp
  k := M.k+3
  two_le_k := by omega
  δ := transition M n
  start_preserved := by
    classical
    intro q a i hi
    apply transition_actions M n a (fun w => (w i).1=none ∧ (w i).2≠.left)
    · simp [hi]
    · intro s; exact (inputMachine M).start_preserved s a i hi
    · intro s; exact (SavedContinuationCall.machine M n initial).start_preserved s a i hi
    · intro s; exact (outputMachine M).start_preserved s a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    apply transition_actions M n a (fun w => (w i).1≠none)
    · exact hi
    · intro s; exact (inputMachine M).start_only_at_start s a i hi
    · intro s; exact (SavedContinuationCall.machine M n initial).start_only_at_start s a i hi
    · intro s; exact (outputMachine M).start_only_at_start s a i hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    classical
    intro q a
    apply transition_actions M n a (fun w => (w ⟨0,by omega⟩).1=a ⟨0,by omega⟩)
    · rfl
    · intro s; exact (inputMachine M).input_readonly s a
    · intro s; exact (SavedContinuationCall.machine M n initial).input_readonly s a
    · intro s; exact (outputMachine M).input_readonly s a

noncomputable def liftInput (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (inputMachine M).Cfg) : (machine M n initial).Cfg where
  state := .inl (q,c.state)
  cells := c.cells
  head := c.head

noncomputable def liftSaved (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (c : (SavedContinuationCall.machine M n initial).Cfg) : (machine M n initial).Cfg where
  state := .inr (.inl c.state)
  cells := c.cells
  head := c.head

noncomputable def liftOutput (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (outputMachine M).Cfg) : (machine M n initial).Cfg where
  state := .inr (.inr (.inl (q,c.state)))
  cells := c.cells
  head := c.head

noncomputable def resumeFrame (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (c : (outputMachine M).Cfg) : (machine M n initial).Cfg where
  state := .inr (.inr (.inr (.inl q)))
  cells := c.cells
  head := c.head

noncomputable def inputParent (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) : (TrackedChildInputBridge.machine M).Cfg where
  state := .before
  cells := fun j => base.cells (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j)
  head := fun j => base.head (FixedTapeExtension.oldTape (TrackedChildInputBridge.machine M) j)

noncomputable def freshInputBase (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) : (inputMachine M).Cfg where
  state := .before
  cells := fun i => if i=FiniteContinuationStack.stackTape M then
    FiniteContinuationStack.freshTape M (base.cells i) rho else base.cells i
  head := fun i => if i=FiniteContinuationStack.stackTape M then rho else base.head i

def parentAfterInput (M : MultitapeTM) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun j => if j=M.outTape then 0 else c.head j

def parentZero (M : MultitapeTM) (c : M.Cfg) : M.Cfg where
  state := c.state
  cells := c.cells
  head := fun _ => 0

noncomputable def inputStart (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M) (freshInputBase M n initial base rho)
    (TrackedChildInputBridge.initialFrame M (inputParent M n initial base) sigma offset extent c v)

noncomputable def inputFinish (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : (inputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedChildInputBridge.machine M) (freshInputBase M n initial base rho)
    (TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y)

noncomputable def callBase (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : (SavedContinuationCall.machine M n initial).Cfg where
  state := .inl (.pushStart q)
  cells := (inputFinish M n initial base rho sigma offset extent c v x y).cells
  head := (inputFinish M n initial base rho sigma offset extent c v x y).head

noncomputable def callParent (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : (TrackedReentrantCall.machine M).Cfg where
  state := (TrackedReentrantCall.machine M).qStart
  cells := (TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y).cells
  head := (TrackedChildInputBridge.finalFrame M (inputParent M n initial base) sigma offset extent c v x y).head

noncomputable def savedStart (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) : (SavedContinuationCall.machine M n initial).Cfg :=
  SavedContinuationCall.callInitialFrame M n initial (callBase M n initial q base rho sigma offset extent c v x y)
    rho q (callParent M n initial base sigma offset extent c v x y) offset extent (parentAfterInput M c)

noncomputable def savedFinish (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (SavedContinuationCall.machine M n initial).Cfg :=
  SavedContinuationCall.callFinalFrame M n initial (callBase M n initial q base rho sigma offset extent c v x y)
    rho q (callParent M n initial base sigma offset extent c v x y) sigma offset extent (parentAfterInput M c) x y T w

noncomputable def outputParent (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (TrackedParentOutputBridge.machine M).Cfg where
  state := .before
  cells := fun j => (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)
  head := fun j => (savedFinish M n initial q base rho sigma offset extent c v x y T w).head
    (FixedTapeExtension.oldTape (TrackedParentOutputBridge.machine M) j)

noncomputable def outputBase (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (outputMachine M).Cfg where
  state := .before
  cells := (savedFinish M n initial q base rho sigma offset extent c v x y T w).cells
  head := (savedFinish M n initial q base rho sigma offset extent c v x y T w).head

noncomputable def outputStart (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (outputBase M n initial q base rho sigma offset extent c v x y T w)
    (TrackedParentOutputBridge.initialFrame M
      (outputParent M n initial q base rho sigma offset extent c v x y T w) sigma offset extent (parentZero M c) w)

noncomputable def outputFinish (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (outputMachine M).Cfg :=
  FixedTapeExtension.embed (TrackedParentOutputBridge.machine M)
    (outputBase M n initial q base rho sigma offset extent c v x y T w)
    (TrackedParentOutputBridge.finalFrame M
      (outputParent M n initial q base rho sigma offset extent c v x y T w) sigma offset extent (parentZero M c) w)

noncomputable def initialFrame (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v : List Bool) : (machine M n initial).Cfg :=
  liftInput M n initial q (inputStart M n initial base rho sigma offset extent c v)

noncomputable def finalFrame (M : MultitapeTM) (n : ℕ) (initial q : Fin n)
    (base : (machine M n initial).Cfg) (rho sigma : ℕ) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (v x y : List Bool) (T : ℕ) (w : List Bool) : (machine M n initial).Cfg :=
  resumeFrame M n initial q (outputFinish M n initial q base rho sigma offset extent c v x y T w)

end IntMul.TrackedMarshalledCall


