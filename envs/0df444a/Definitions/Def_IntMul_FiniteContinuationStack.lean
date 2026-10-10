-- Prove2me | Definitions.Def_IntMul_FiniteContinuationStack
-- name    : IntMul_FiniteContinuationStack
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:50:12.057787+00:00
-- url     : https://prove2.me/theorems/c6e667d9-bf9c-4ddc-b57b-4f21156fbe14
-- title:
--   Physical finite-control continuation stack on one additional fixed tape
-- statement:
--   For a finite control-label set of size n, a fixed finite service table stores each label as n one-hot bits after a local separator on one added stack tape. The tagged alphabet is shared with the tracked bank services; the total tape count is k+3. Push writes the separator and all bits by actual transitions. Pop reads and erases the bits right to left into a finite control register, erases the separator, and enters the recovered label's finite resume state. All other tapes and heads stay fixed, and arbitrary older stack prefixes are retained. Every counter and label ranges over a fixed finite set depending only on n, never on input length or recursion depth. The default completed-push branch performs one charged dispatch to pop; a caller may instead intercept it to run a child. Resume states are return-control states distinct from the designated global halt.
-- source:
--   Original physical finite continuation stack for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.FiniteContinuationStack

open IntMul.TrackedBankedSimulation (Sym)

/-- Every index and label is finite, fixed by the caller's control size n.
There is no input-dependent counter or recursion-depth-dependent state set. -/
inductive State (n : ℕ)
  | pushStart (q : Fin n)
  | pushBit (q j : Fin n)
  | pushDone
  | popStart
  | popBit (j : Fin n) (found : Option (Fin n))
  | popMarker (found : Option (Fin n))
  | resume (q : Fin n)
  | error
  | halt
  deriving DecidableEq

instance (n : ℕ) : Fintype (State n) where
  elems := (Finset.univ.image (fun q : Fin n => State.pushStart q)) ∪
    (Finset.univ.image (fun qj : Fin n × Fin n => State.pushBit qj.1 qj.2)) ∪
    (Finset.univ.image (fun jf : Fin n × Option (Fin n) => State.popBit jf.1 jf.2)) ∪
    (Finset.univ.image (fun f : Option (Fin n) => State.popMarker f)) ∪
    (Finset.univ.image (fun q : Fin n => State.resume q)) ∪
    {.pushDone,.popStart,.error,.halt}
  complete := by
    intro q
    cases q <;> simp

def stackTape (M : MultitapeTM) : Fin (M.k + 3) := ⟨M.k + 2,by omega⟩

noncomputable def rawTransition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) : State n × (Fin (M.k + 3) → Sym M × Move) := by
  classical
  exact match q with
  | .pushStart q => (.pushBit q ⟨0,by have := q.isLt; omega⟩,fun i =>
      (if i = stackTape M then some (M.sep,true) else a i,
        if i = stackTape M then .right else .stay))
  | .pushBit q j =>
      (if h : j.val + 1 < n then .pushBit q ⟨j.val + 1,h⟩ else .pushDone,
        fun i => (if i = stackTape M then some (M.bitSym (decide (j.val = q.val)),true) else a i,
          if i = stackTape M then .right else .stay))
  | .pushDone => (.popStart,fun i => (a i,.stay))
  | .popStart =>
      if h : 0 < n then (.popBit ⟨0,h⟩ none,fun i => (a i,if i = stackTape M then .left else .stay))
      else (.popMarker none,fun i => (a i,.stay))
  | .popBit j found =>
      let found' := if TrackedBankedSimulation.decode M (a (stackTape M)) = M.one then
        some (⟨n - 1 - j.val,by have := j.isLt; omega⟩ : Fin n) else found
      (if h : j.val + 1 < n then .popBit ⟨j.val + 1,h⟩ found' else .popMarker found',
        fun i => (if i = stackTape M then some (M.blank,false) else a i,
          if i = stackTape M then .left else .stay))
  | .popMarker found =>
      (if a (stackTape M) = some (M.sep,true) then
          match found with | some q => .resume q | none => .error
        else .error,
        fun i => (if i = stackTape M then some (M.blank,false) else a i,.stay))
  | .resume q => (.resume q,fun i => (a i,.stay))
  | .error => (.error,fun i => (a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) : State n × (Fin (M.k + 3) → Sym M × Move) :=
  let r := rawTransition M n q a
  (r.1,fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem raw_other (M : MultitapeTM) (n : ℕ) (q : State n)
    (a : Fin (M.k + 3) → Sym M) (i : Fin (M.k + 3)) (hi : i ≠ stackTape M) :
    (rawTransition M n q a).2 i = (a i,.stay) := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;> simp_all

/-- A single finite continuation-table service on one additional fixed tape.
The table can be inlined into a caller that dispatches at pushDone/resume q.
The default pushDone branch physically dispatches to pop for a round trip. -/
noncomputable abbrev machine (M : MultitapeTM) (n : ℕ) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State n
  qStart := .popStart
  qHalt := .halt
  start_ne_halt := by simp
  k := M.k + 3
  two_le_k := by omega
  δ := transition M n
  start_preserved := by
    classical
    intro q a i hi
    change (TrackedBankCleanup.protect M (a i) _ _).1 = none ∧
      (TrackedBankCleanup.protect M (a i) _ _).2 ≠ .left
    rw [hi]
    simp only [TrackedBankCleanup.protect]
    split <;> simp_all
  start_only_at_start := by
    classical
    intro q a i hi
    change (TrackedBankCleanup.protect M (a i) _ _).1 ≠ none
    cases hs : a i with
    | none => exact False.elim (hi hs)
    | some s => simp only [TrackedBankCleanup.protect]; split <;> simp
  halt_fixed := by intro a; simp [transition,rawTransition,protect_same_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M n q a).2 ⟨0,by omega⟩).1
      ((rawTransition M n q a).2 ⟨0,by omega⟩).2).1 = _
    rw [raw_other M n q a ⟨0,by omega⟩ (by intro h; have := congrArg Fin.val h; simp [stackTape] at this)]
    simp only [protect_same_stay]

def freshTape (M : MultitapeTM) (base : ℕ → Sym M) (rho p : ℕ) : Sym M :=
  if p < rho then base p else some (M.blank,false)

/-- j physically written one-hot bits; the remainder is genuinely fresh. -/
def recordTape (M : MultitapeTM) (n : ℕ) (base : ℕ → Sym M) (rho : ℕ) (q : Fin n) (j p : ℕ) : Sym M :=
  if p < rho then base p else if p = rho then some (M.sep,true)
    else if p < rho + j + 1 then some (M.bitSym (decide (p - rho - 1 = q.val)),true)
    else some (M.blank,false)

noncomputable def pushStartFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (q : Fin n) : (machine M n).Cfg where
  state := .pushStart q
  cells := fun i => if i = stackTape M then freshTape M (base.cells i) rho else base.cells i
  head := fun i => if i = stackTape M then rho else base.head i

noncomputable def pushFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (q : Fin n) (j : ℕ) : (machine M n).Cfg where
  state := if h : j < n then .pushBit q ⟨j,h⟩ else .pushDone
  cells := fun i => if i = stackTape M then recordTape M n (base.cells i) rho q j else base.cells i
  head := fun i => if i = stackTape M then rho + j + 1 else base.head i

noncomputable def popStartFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (q : Fin n) : (machine M n).Cfg where
  state := .popStart
  cells := (pushFrame M n base rho q n).cells
  head := (pushFrame M n base rho q n).head

def recovered (n : ℕ) (q : Fin n) (j : ℕ) : Option (Fin n) :=
  if n - q.val ≤ j then some q else none

noncomputable def popFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (q : Fin n) (j : ℕ) : (machine M n).Cfg where
  state := if h : j < n then .popBit ⟨j,h⟩ (recovered n q j) else .popMarker (recovered n q j)
  cells := fun i => if i = stackTape M then recordTape M n (base.cells i) rho q (n - j) else base.cells i
  head := fun i => if i = stackTape M then rho + (n - j) else base.head i

noncomputable def finalFrame (M : MultitapeTM) (n : ℕ) (base : (machine M n).Cfg)
    (rho : ℕ) (q : Fin n) : (machine M n).Cfg where
  state := .resume q
  cells := (pushStartFrame M n base rho q).cells
  head := (pushStartFrame M n base rho q).head

end IntMul.FiniteContinuationStack


