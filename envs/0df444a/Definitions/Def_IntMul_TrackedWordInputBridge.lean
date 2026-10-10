-- Prove2me | Definitions.Def_IntMul_TrackedWordInputBridge
-- name    : IntMul_TrackedWordInputBridge
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T01:14:15.718986+00:00
-- url     : https://prove2.me/theorems/820da2b4-9472-4b6d-965b-1d11abc3ae1d
-- title:
--   Generic finite-alphabet physical word transfer with old-buffer tail erasure
-- statement:
--   The same fixed five-state physical copying, clearing and rewinding algorithm, with proof frames generalized to any finite word over zero, one and the separator, including an empty word. The word validity subtype is only a mathematical proof parameter and is never passed to delta. All old caller-buffer tail cells are actually erased, every source-bank cell and flag is retained, and the source and buffer heads are physically restored. This generalization supports physical replacement of a previously returned shared buffer by a new child or parent result.
-- source:
--   Original generic physical word-transfer frames for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankPreparation
import Definitions.Def_IntMul_TrackedOutputReturn

namespace IntMul.TrackedWordInputBridge

open IntMul.TrackedBankedSimulation (Sym)

/-- A proof-frame word over the finite symbols accepted by the transfer.
No word data is supplied to delta. -/
abbrev ValidWord (M : MultitapeTM) := {w : List M.Sym // ∀ a ∈ w, a=M.zero ∨ a=M.one ∨ a=M.sep}
def word (M : MultitapeTM) (w : ValidWord M) : List M.Sym := w.val


inductive State
  | before | copy | clearTail | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.before,.copy,.clearTail,.rewind,.halt}
  complete := by intro q; cases q <;> simp

def bufferTape (M : MultitapeTM) : Fin (M.k + 2) := ⟨1,by omega⟩
def packetTape (M : MultitapeTM) : Fin (M.k + 2) := BankedSimulation.workTape M M.outTape

noncomputable def rawTransition (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .before =>
      if a (bufferTape M) = some (M.startSym,true) ∧ a (packetTape M) = some (M.startSym,true) then
        (.copy,fun i => (a i,if i = bufferTape M ∨ i = packetTape M then .right else .stay))
      else (.before,fun i => (a i,if (i = bufferTape M ∨ i = packetTape M) ∧ a i ≠ some (M.startSym,true)
        then .left else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a (packetTape M)) = M.zero ∨
          TrackedBankedSimulation.decode M (a (packetTape M)) = M.one ∨
          TrackedBankedSimulation.decode M (a (packetTape M)) = M.sep then
        (.copy,fun i =>
          (if i = bufferTape M then some (TrackedBankedSimulation.decode M (a (packetTape M)),true) else a i,
            if i = bufferTape M ∨ i = packetTape M then .right else .stay))
      else (.clearTail,fun i => (a i,.stay))
  | .clearTail =>
      if TrackedBankCleanup.visited M (a (bufferTape M)) = true then
        (.clearTail,fun i => (if i = bufferTape M then some (M.blank,false) else a i,
          if i = bufferTape M then .right else .stay))
      else (.rewind,fun i => (a i,if i = bufferTape M ∨ i = packetTape M then .left else .stay))
  | .rewind =>
      if a (bufferTape M) = some (M.startSym,true) ∧ a (packetTape M) = some (M.startSym,true) then
        (.halt,fun i => (if i = bufferTape M then some (M.blank,false) else a i,.stay))
      else (.rewind,fun i => (a i,if (i = bufferTape M ∨ i = packetTape M) ∧ a i ≠ some (M.startSym,true)
        then .left else .stay))
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
    simp [bufferTape,packetTape,BankedSimulation.workTape,MultitapeTM.outTape]

/-- Physically move an existing parent request packet into the caller buffer,
clearing any old returned-output tail and retaining all parent cells/flags.
All offsets, lengths and extents occur in proof frames only. -/
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

noncomputable def parentBase (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ) (v : List Bool) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i = bufferTape M then TrackedOutputReturn.bufferTape M (base.cells i) sigma v else base.cells i
  head := fun i => if i = bufferTape M then sigma + v.length + 1 else base.head i

noncomputable def initialCells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) :
    Fin (M.k + 2) → ℕ → Sym M :=
  (TrackedBankedSimulation.embed M (parentBase M base sigma v) offset extent c).cells

noncomputable def initialHeads (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : Fin (M.k + 2) → ℕ :=
  (TrackedBankedSimulation.embed M (parentBase M base sigma v) offset extent c).head

noncomputable def beforeFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (r : ℕ) : (machine M).Cfg where
  state := .before
  cells := initialCells M base sigma offset extent c v
  head := fun i => if i = bufferTape M then sigma + (v.length + 1 - r)
    else if i = packetTape M then offset M.outTape + (c.head M.outTape - r)
    else initialHeads M base sigma offset extent c v i

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) : (machine M).Cfg :=
  beforeFrame M base sigma offset extent c v 0

def copiedTape (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (j p : ℕ) : Sym M :=
  if p < sigma then base p else if p = sigma then some (M.startSym,true)
    else if p < sigma + j + 1 then some (w.getD (p - sigma - 1) M.blank,true)
    else TrackedOutputReturn.bufferTape M base sigma v p

def clearedTape (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List M.Sym) (v : List Bool) (d p : ℕ) : Sym M :=
  if p < sigma then base p else if p = sigma then some (M.startSym,true)
    else if p < sigma + w.length + 1 then some (w.getD (p - sigma - 1) M.blank,true)
    else if p < sigma + w.length + d + 1 then some (M.blank,false)
    else TrackedOutputReturn.bufferTape M base sigma v p

noncomputable def copyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (j : ℕ) : (machine M).Cfg where
  state := .copy
  cells := fun i => if i = bufferTape M then copiedTape M (base.cells i) sigma (word M w) v j
    else initialCells M base sigma offset extent c v i
  head := fun i => if i = bufferTape M then sigma + j + 1 else if i = packetTape M then offset M.outTape + j + 1
    else initialHeads M base sigma offset extent c v i

noncomputable def clearFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (d : ℕ) : (machine M).Cfg where
  state := .clearTail
  cells := fun i => if i = bufferTape M then clearedTape M (base.cells i) sigma (word M w) v d
    else initialCells M base sigma offset extent c v i
  head := fun i => if i = bufferTape M then sigma + (word M w).length + d + 1
    else if i = packetTape M then offset M.outTape + (word M w).length + 1
    else initialHeads M base sigma offset extent c v i

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) (r : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := fun i => if i = bufferTape M then TrackedBankPreparation.bankTape M (base.cells i) sigma (word M w)
    else initialCells M base sigma offset extent c v i
  head := fun i => if i = bufferTape M then sigma + (max (word M w).length v.length - r)
    else if i = packetTape M then offset M.outTape + ((word M w).length - r)
    else initialHeads M base sigma offset extent c v i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool)
    (w : ValidWord M) : (machine M).Cfg where
  state := .halt
  cells := fun i => if i = bufferTape M then TrackedBankPreparation.sourceTape M (base.cells i) sigma (word M w)
    else initialCells M base sigma offset extent c v i
  head := fun i => if i = bufferTape M then sigma else if i = packetTape M then offset M.outTape
    else initialHeads M base sigma offset extent c v i

end IntMul.TrackedWordInputBridge


