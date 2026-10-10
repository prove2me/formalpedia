-- Prove2me | Definitions.Def_IntMul_InteriorBankedCall
-- name    : IntMul_InteriorBankedCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T21:23:04.691467+00:00
-- url     : https://prove2.me/theorems/244b9a4e-7fd0-45d4-a236-c771941507f5
-- title:
--   Literal child caller in arbitrary interior banks with saved caller prefixes
-- statement:
--   For each finite child machine M, defines one fixed M.k+2-tape caller over Option M.Sym with seven finite phases plus M.K. Global input tape zero is frozen. A caller-computed input buffer on tape one and fresh suffix banks on the remaining tapes are represented by proof-side frames at arbitrary boundary positions. The finite table physically creates local markers, copies and erases the buffer, rewinds the child input, executes the literal child table, independently rewinds both the erased buffer and child output, copies the output back to the buffer, and halts. All offsets, lengths and full configurations are proof data only, absent from the transition table. Saved prefixes lie strictly before the chosen boundaries. Buffer production, fresh bank allocation and recursive continuation management remain separate charged obligations.
-- source:
--   Original finite-tape compiler foundation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_BankedCall

namespace IntMul.InteriorBankedCall

open IntMul.BankedCall (Phase)
abbrev State (M : MultitapeTM) := BankedCall.State M

/-- Buffer tape one supplies caller-computed child input. The first transition
writes every local boundary marker; the copy erases the buffer as it reads it. -/
noncomputable def rawTransition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Option M.Sym) : State M × (Fin (M.k + 2) → Option M.Sym × Move) := by
  classical
  exact match q with
  | .inr q =>
      if q = M.qHalt then (.inl .rewindOutput,fun i => (a i,.stay))
      else let r := BankedSimulation.transition M q a
        (.inr r.1,r.2)
  | .inl .start | .inl .mark => (.inl .copyInput,fun i =>
      (if 1 ≤ i.val then some M.startSym else a i,
        if i.val = 1 ∨ i.val = 2 then .right else .stay))
  | .inl .copyInput =>
      if a ⟨1,by omega⟩ = some M.zero ∨ a ⟨1,by omega⟩ = some M.one ∨ a ⟨1,by omega⟩ = some M.sep then
        (.inl .copyInput,fun i =>
          (if i.val = 1 then some M.blank else if i.val = 2 then a ⟨1,by omega⟩ else a i,
            if i.val = 1 ∨ i.val = 2 then .right else .stay))
      else (.inl .rewindInput,fun i => (a i,if i.val = 2 then .left else .stay))
  | .inl .rewindInput =>
      if a ⟨2,by have := M.two_le_k; omega⟩ = some M.startSym then
        (.inr M.qStart,fun i => (a i,.stay))
      else (.inl .rewindInput,fun i => (a i,if i.val = 2 then .left else .stay))
  | .inl .rewindOutput =>
      if a ⟨1,by omega⟩ = some M.startSym ∧ a ⟨3,by have := M.two_le_k; omega⟩ = some M.startSym then
        (.inl .copyOutput,fun i => (a i,if i.val = 1 ∨ i.val = 3 then .right else .stay))
      else (.inl .rewindOutput,fun i =>
        (a i,if (i.val = 1 ∨ i.val = 3) ∧ a i ≠ some M.startSym then .left else .stay))
  | .inl .copyOutput =>
      if a ⟨3,by have := M.two_le_k; omega⟩ = some M.zero ∨
          a ⟨3,by have := M.two_le_k; omega⟩ = some M.one then
        (.inl .copyOutput,fun i =>
          (if i.val = 1 then a ⟨3,by have := M.two_le_k; omega⟩ else a i,
            if i.val = 1 ∨ i.val = 3 then .right else .stay))
      else (.inl .halt,fun i => (a i,.stay))
  | .inl .halt => (.inl .halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Option M.Sym) : State M × (Fin (M.k + 2) → Option M.Sym × Move) :=
  match q with
  | .inr _ => rawTransition M q a
  | .inl _ =>
      let r := rawTransition M q a
      (r.1,fun i => BankedSimulation.protect M (a i) (BankedSimulation.decode M (r.2 i).1) (r.2 i).2)

private theorem protect_self_stay (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .stay = (a,.stay) := by
  cases a <;> rfl

private theorem protect_self_write (M : MultitapeTM) (a : Option M.Sym) (d : Move) :
    (BankedSimulation.protect M a (BankedSimulation.decode M a) d).1 = a := by
  cases a <;> rfl

private theorem raw_input_readonly (M : MultitapeTM) (q : Phase)
    (a : Fin (M.k + 2) → Option M.Sym) :
    ((rawTransition M (.inl q) a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  classical
  cases q <;> simp only [rawTransition] <;> split_ifs <;> first | rfl | omega

/-- A fixed finite child caller for fresh interior suffix banks. All positions
are held by physical heads, never read as numbers by the transition table. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Option M.Sym
  blank := some M.blank
  startSym := none
  zero := some M.zero
  one := some M.one
  sep := some M.sep
  syms_distinct := (BankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl .start
  qHalt := .inl .halt
  start_ne_halt := by simp
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        simp only [transition]
        rw [hi]
        simp only [BankedSimulation.protect]
        split <;> simp_all
    | inr q =>
        by_cases hq : q = M.qHalt
        · simp [transition,rawTransition,hq,hi]
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        simp only [transition]
        cases hs : a i with
        | none => exact False.elim (hi hs)
        | some s => simp [BankedSimulation.protect]
    | inr q =>
        by_cases hq : q = M.qHalt
        · simpa [transition,rawTransition,hq] using hi
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).start_only_at_start q a i hi
  halt_fixed := by
    classical
    intro a
    simp [transition,rawTransition,protect_self_stay]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        change (BankedSimulation.protect M (a ⟨0,by omega⟩)
          (BankedSimulation.decode M ((rawTransition M (.inl q) a).2 ⟨0,by omega⟩).1) _).1 = _
        rw [raw_input_readonly]
        exact protect_self_write _ _ _
    | inr q =>
        by_cases hq : q = M.qHalt
        · simp [transition,rawTransition,hq]
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).input_readonly q a

/-- A tagged child tape after an arbitrary saved prefix. -/
def bankTape (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) : Option M.Sym :=
  if p < offset then base p else some (M.tapeOf w (p - offset))

/-- A fresh unused bank suffix; physically writing its local marker is charged. -/
def freshTape (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ) (p : ℕ) : Option M.Sym :=
  if p < offset then base p else some M.blank

/-- A reserved blank boundary followed by caller-computed child input and a
blank tail. Creating that payload is a separate caller computation. -/
def sourceTape (M : MultitapeTM) (base : ℕ → Option M.Sym) (offset : ℕ)
    (w : List M.Sym) (p : ℕ) : Option M.Sym :=
  if p < offset then base p else if p = offset then some M.blank
    else some (w.getD (p - offset - 1) M.blank)

/-- The caller has computed the child input buffer and reserved fresh bank
suffixes. Its heads name the boundaries; this frame has no local markers yet. -/
noncomputable def inputFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) : (machine M).Cfg where
  state := .inl .start
  cells := fun i => if h : 2 ≤ i.val then
    freshTape M (base.cells i) (offset (BankedSimulation.innerTape M i h))
    else if i.val = 1 then sourceTape M (base.cells i) sigma (BankedCall.inputWord M x y)
    else base.cells i
  head := fun i => if h : 2 ≤ i.val then offset (BankedSimulation.innerTape M i h)
    else if i.val = 1 then sigma else base.head i

/-- After copy-and-erase, the mutable buffer retains its saved prefix and new
local marker, with an entirely blank suffix. Its head is on the end blank. -/
noncomputable def callerBase (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (x y : List Bool) : (BankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i.val = 1 then bankTape M (base.cells i) sigma [] else base.cells i
  head := fun i => if i.val = 1 then sigma + (BankedCall.inputWord M x y).length + 1 else base.head i

noncomputable def runningFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg) : (machine M).Cfg where
  state := .inr c.state
  cells := (BankedSimulation.embed M (callerBase M base sigma x y) offset c).cells
  head := (BankedSimulation.embed M (callerBase M base sigma x y) offset c).head

noncomputable def readyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) : (machine M).Cfg :=
  runningFrame M base sigma offset x y (M.initCfg x y)

/-- The input buffer's first j payload cells have been physically erased. -/
def copyTape (M : MultitapeTM) (base : ℕ → Option M.Sym) (sigma : ℕ)
    (w : List M.Sym) (j p : ℕ) : Option M.Sym :=
  if p < sigma then base p else if p = sigma then some M.startSym
    else if p < sigma + j + 1 then some M.blank
    else some (w.getD (p - sigma - 1) M.blank)

noncomputable def copyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inl .copyInput
  cells := fun i => if h : 2 ≤ i.val then
    bankTape M (base.cells i) (offset (BankedSimulation.innerTape M i h))
      (if i.val = 2 then (BankedCall.inputWord M x y).take j else [])
    else if i.val = 1 then copyTape M (base.cells i) sigma (BankedCall.inputWord M x y) j
    else base.cells i
  head := fun i => if h : 2 ≤ i.val then
    offset (BankedSimulation.innerTape M i h) + (if i.val = 2 then j + 1 else 0)
    else if i.val = 1 then sigma + j + 1 else base.head i

noncomputable def returnInputFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (p : ℕ) : (machine M).Cfg where
  state := .inl .rewindInput
  cells := (readyFrame M base sigma offset x y).cells
  head := fun i => if h : 2 ≤ i.val then
    offset (BankedSimulation.innerTape M i h) + (if i.val = 2 then p else 0)
    else if i.val = 1 then sigma + (BankedCall.inputWord M x y).length + 1 else base.head i

/-- Both return heads can finish independently; remaining distances a,b are
proof data only. The table tests the two scanned local markers. -/
noncomputable def returnOutputFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg) (a b : ℕ) : (machine M).Cfg where
  state := .inl .rewindOutput
  cells := (runningFrame M base sigma offset x y c).cells
  head := fun i => if i.val = 1 then sigma + a else if i.val = 3 then offset M.outTape + b
    else (runningFrame M base sigma offset x y c).head i

/-- The restored buffer now holds the returned output, with its saved prefix
and local marker retained. Every other bank retains the child's final cells. -/
noncomputable def copyOutputFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inl .copyOutput
  cells := fun i => if i.val = 1 then bankTape M (base.cells i) sigma ((w.take j).map M.bitSym)
    else (runningFrame M base sigma offset x y c).cells i
  head := fun i => if i.val = 1 then sigma + j + 1 else if i.val = 3 then offset M.outTape + j + 1
    else (runningFrame M base sigma offset x y c).head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) : (machine M).Cfg where
  state := .inl .halt
  cells := (copyOutputFrame M base sigma offset x y c w w.length).cells
  head := (copyOutputFrame M base sigma offset x y c w w.length).head

end IntMul.InteriorBankedCall


