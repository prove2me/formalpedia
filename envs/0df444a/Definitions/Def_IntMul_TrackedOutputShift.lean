-- Prove2me | Definitions.Def_IntMul_TrackedOutputShift
-- name    : IntMul_TrackedOutputShift
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:06:47.963133+00:00
-- url     : https://prove2.me/theorems/7d357ecd-a877-4df6-ab9e-b59722ac7425
-- title:
--   Physical finite-register shift of a returned word to the native output origin
-- statement:
--   Seven fixed finite states on the existing M.k+2 tapes and Option(M.Sym×Bool) alphabet rewind a returned output buffer to its local marker at cell one, then shift each bit left by one cell using a single Boolean held in finite control. A read/left step loads the bit, a write/right step stores it in its new position, and an advance/right step moves to the next unread bit. The first blank dispatches to a physical final erase, clearing the last duplicate or the empty-word local marker. The global marker at zero and all other tape cells and heads are preserved. The terminal output starts at native cell one with a fresh blank tail. Delta contains no output length, address or oracle.
-- source:
--   Original physical finite-register native output placement for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedOutputReturn

namespace IntMul.TrackedOutputShift

open IntMul.TrackedBankedSimulation (Sym)

inductive State
  | rewind | read | write (bit : Bool) | advance | erase | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.read,.write false,.write true,.advance,.erase,.halt}
  complete := by intro q; cases q <;> simp;

noncomputable def rawTransition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .rewind =>
      if a ⟨1,by omega⟩ = some (M.startSym,true) then
        (.read,fun i => (a i,if i.val = 1 then .right else .stay))
      else (.rewind,fun i => (a i,if i.val = 1 then .left else .stay))
  | .read =>
      if TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.zero then
        (.write false,fun i => (a i,if i.val = 1 then .left else .stay))
      else if TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.one then
        (.write true,fun i => (a i,if i.val = 1 then .left else .stay))
      else (.erase,fun i => (a i,if i.val = 1 then .left else .stay))
  | .write b => (.advance,fun i =>
      (if i.val = 1 then some (M.bitSym b,true) else a i,if i.val = 1 then .right else .stay))
  | .advance => (.read,fun i => (a i,if i.val = 1 then .right else .stay))
  | .erase => (.halt,fun i => (if i.val = 1 then some (M.blank,false) else a i,.stay))
  | .halt => (.halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) :=
  let r := rawTransition M q a
  (r.1,fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_self_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem raw_input_readonly (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    ((rawTransition M q a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  classical
  cases q with
  | rewind => dsimp only [rawTransition]; split <;> rfl
  | read =>
      dsimp only [rawTransition]
      split
      · rfl
      · split <;> rfl
  | write b =>
      change (if (0 : ℕ) = 1 then some (M.bitSym b,true) else a ⟨0,by omega⟩) = _
      rw [if_neg (by omega : ¬(0 : ℕ) = 1)]
  | advance => rfl
  | erase =>
      change (if (0 : ℕ) = 1 then some (M.blank,false) else a ⟨0,by omega⟩) = _
      rw [if_neg (by omega : ¬(0 : ℕ) = 1)]
  | halt => rfl

/-- Seven finite states shift the returned bits left by one cell into the
native output origin, overwrite/erase the local marker, and clear the last
duplicated bit. Every seek, register load, write and advance is charged. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .rewind
  qHalt := .halt
  start_ne_halt := by decide
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
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
  halt_fixed := by intro a; simp [transition,rawTransition,protect_self_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M q a).2 ⟨0,by omega⟩).1 _).1 = _
    rw [raw_input_readonly]
    cases a ⟨0,by omega⟩ <;> rfl

def mixedTape (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (j p : ℕ) : Sym M :=
  if p = 0 then base 0 else if p ≤ j then some ((w.map M.bitSym).getD (p - 1) M.blank,true)
    else TrackedOutputReturn.bufferTape M base 1 w p

def outputTape (M : MultitapeTM) (base : ℕ → Sym M) (w : List Bool) (p : ℕ) : Sym M :=
  if p = 0 then base 0 else some ((w.map M.bitSym).getD (p - 1) M.blank,decide (p - 1 < w.length))

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (p : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := fun i => if i.val = 1 then TrackedOutputReturn.bufferTape M (base.cells i) 1 w else base.cells i
  head := fun i => if i.val = 1 then p else base.head i

noncomputable def readFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .read
  cells := fun i => if i.val = 1 then mixedTape M (base.cells i) w j else base.cells i
  head := fun i => if i.val = 1 then j + 2 else base.head i

noncomputable def writeFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) (b : Bool) : (machine M).Cfg where
  state := .write b
  cells := (readFrame M base w j).cells
  head := fun i => if i.val = 1 then j + 1 else base.head i

noncomputable def advanceFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .advance
  cells := (readFrame M base w (j + 1)).cells
  head := fun i => if i.val = 1 then j + 2 else base.head i

noncomputable def eraseFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) : (machine M).Cfg where
  state := .erase
  cells := (readFrame M base w w.length).cells
  head := fun i => if i.val = 1 then w.length + 1 else base.head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg) (w : List Bool) : (machine M).Cfg where
  state := .halt
  cells := fun i => if i.val = 1 then outputTape M (base.cells i) w else base.cells i
  head := fun i => if i.val = 1 then w.length + 1 else base.head i

end IntMul.TrackedOutputShift


