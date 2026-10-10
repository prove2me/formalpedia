-- Prove2me | Definitions.Def_IntMul_TrackedParentOutputBridge
-- name    : IntMul_TrackedParentOutputBridge
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T00:36:00.593378+00:00
-- url     : https://prove2.me/theorems/8ccbb6ba-9e89-439f-9eaa-905acfb5b2ee
-- title:
--   Physical child-result placement, old parent-tail erasure and output-head restoration
-- statement:
--   A fixed five-state machine on k+2 shared tapes and the common tagged alphabet physically copies a returned bit word from the caller buffer into an already restored parent output bank. It overwrites the old payload, erases every excess visited cell including visited blank tails, physically rewinds the parent output head and retains its local marker. The complete caller buffer and every other parent tape and head remain exact. No word length, offset or extent enters the finite transition table.
-- source:
--   Original physical parent-output bridge for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankPreparation
import Definitions.Def_IntMul_TrackedOutputReturn

namespace IntMul.TrackedParentOutputBridge

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.TrackedBankPreparation (inputWord)

inductive State
  | before | copy | clearTail | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.before,.copy,.clearTail,.rewind,.halt}
  complete := by intro q; cases q <;> simp

def bufferTape (M : MultitapeTM) : Fin (M.k + 2) := ⟨1,by omega⟩
def targetTape (M : MultitapeTM) : Fin (M.k + 2) := BankedSimulation.workTape M M.outTape

noncomputable def rawTransition (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .before =>
      if a (bufferTape M) = some (M.startSym,true) ∧ a (targetTape M) = some (M.startSym,true) then
        (.copy,fun i => (a i,if i = bufferTape M ∨ i = targetTape M then .right else .stay))
      else (.before,fun i => (a i,if i = bufferTape M ∧ a i ≠ some (M.startSym,true) then .left else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a (bufferTape M)) = M.zero ∨
          TrackedBankedSimulation.decode M (a (bufferTape M)) = M.one then
        (.copy,fun i =>
          (if i = targetTape M then some (TrackedBankedSimulation.decode M (a (bufferTape M)),true) else a i,
            if i = bufferTape M ∨ i = targetTape M then .right else .stay))
      else (.clearTail,fun i => (a i,.stay))
  | .clearTail =>
      if TrackedBankCleanup.visited M (a (targetTape M)) = true then
        (.clearTail,fun i => (if i = targetTape M then some (M.blank,false) else a i,
          if i = targetTape M then .right else .stay))
      else (.rewind,fun i => (a i,if i = targetTape M then .left else .stay))
  | .rewind =>
      if a (targetTape M) = some (M.startSym,true) then
        (.halt,fun i => (a i,.stay))
      else (.rewind,fun i => (a i,if i = targetTape M then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    State × (Fin (M.k + 2) → Sym M × Move) :=
  let r := rawTransition M q a
  (r.1,fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_same_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem raw_input (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    ((rawTransition M q a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  classical
  cases q <;> dsimp only [rawTransition] <;> split_ifs <;>
    simp [bufferTape,targetTape,BankedSimulation.workTape,MultitapeTM.outTape]

/-- Physically place a returned child word in the restored parent output bank,
clearing its old visited tail and retaining all other banks and the buffer.
All offsets, lengths and extents occur only in proof frames. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .before
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
  halt_fixed := by intro a; simp [transition,rawTransition,protect_same_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M q a).2 ⟨0,by omega⟩).1 _).1 = _
    rw [raw_input]
    cases a ⟨0,by omega⟩ <;> rfl

noncomputable def parentBase (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ) (w : List Bool) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i = bufferTape M then TrackedOutputReturn.bufferTape M (base.cells i) sigma w else base.cells i
  head := fun i => if i = bufferTape M then sigma + w.length + 1 else base.head i

noncomputable def initialCells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    Fin (M.k + 2) → ℕ → Sym M :=
  (TrackedBankedSimulation.embed M (parentBase M base sigma w) offset extent c).cells

noncomputable def initialHeads (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : Fin (M.k + 2) → ℕ :=
  fun i => if i = targetTape M then offset M.outTape else
    (TrackedBankedSimulation.embed M (parentBase M base sigma w) offset extent c).head i

noncomputable def beforeFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) : (machine M).Cfg where
  state := .before
  cells := initialCells M base sigma offset extent c w
  head := fun i => if i = bufferTape M then sigma + (w.length + 1 - r)
    else initialHeads M base sigma offset extent c w i

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : (machine M).Cfg :=
  beforeFrame M base sigma offset extent c w 0

def oldTape (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (p : ℕ) : Sym M :=
  if p < offset then base p else some (cells (p-offset),decide (p-offset ≤ extent))

def copiedTape (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (j p : ℕ) : Sym M :=
  if p < offset then base p else if p = offset then some (M.startSym,true)
    else if p < offset + j + 1 then some ((w.map M.bitSym).getD (p-offset-1) M.blank,true)
    else oldTape M base offset extent cells p

def clearedTape (M : MultitapeTM) (base : ℕ → Sym M) (offset extent : ℕ)
    (cells : ℕ → M.Sym) (w : List Bool) (d p : ℕ) : Sym M :=
  if p < offset then base p else if p = offset then some (M.startSym,true)
    else if p < offset + w.length + 1 then some ((w.map M.bitSym).getD (p-offset-1) M.blank,true)
    else if p < offset + w.length + d + 1 then some (M.blank,false)
    else oldTape M base offset extent cells p

noncomputable def copyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .copy
  cells := fun i => if i = targetTape M then copiedTape M (base.cells i) (offset M.outTape) (extent M.outTape)
    (c.cells M.outTape) w j else initialCells M base sigma offset extent c w i
  head := fun i => if i = bufferTape M then sigma+j+1 else if i = targetTape M then offset M.outTape+j+1
    else initialHeads M base sigma offset extent c w i

noncomputable def clearFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (d : ℕ) : (machine M).Cfg where
  state := .clearTail
  cells := fun i => if i = targetTape M then clearedTape M (base.cells i) (offset M.outTape) (extent M.outTape)
    (c.cells M.outTape) w d else initialCells M base sigma offset extent c w i
  head := fun i => if i = bufferTape M then sigma+w.length+1
    else if i = targetTape M then offset M.outTape+w.length+d+1
    else initialHeads M base sigma offset extent c w i

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (r : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := fun i => if i = targetTape M then TrackedBankPreparation.bankTape M (base.cells i) (offset M.outTape)
    (w.map M.bitSym) else initialCells M base sigma offset extent c w i
  head := fun i => if i = bufferTape M then sigma+w.length+1
    else if i = targetTape M then offset M.outTape+(max w.length (extent M.outTape)-r)
    else initialHeads M base sigma offset extent c w i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : (machine M).Cfg where
  state := .halt
  cells := fun i => if i = targetTape M then TrackedBankPreparation.bankTape M (base.cells i) (offset M.outTape)
    (w.map M.bitSym) else initialCells M base sigma offset extent c w i
  head := fun i => if i = bufferTape M then sigma+w.length+1 else if i = targetTape M then offset M.outTape
    else initialHeads M base sigma offset extent c w i

end IntMul.TrackedParentOutputBridge


