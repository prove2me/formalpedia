-- Prove2me | Definitions.Def_IntMul_TrackedBankPreparation
-- name    : IntMul_TrackedBankPreparation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T22:39:52.391745+00:00
-- url     : https://prove2.me/theorems/4447b75f-7ea4-44f8-a5d1-0570f9cdc06c
-- title:
--   Physical copy-and-erase preparation of child banks with exact initial visited flags
-- statement:
--   For every finite child machine M, defines a fixed M.k+2-tape four-state initializer over the finite tracked alphabet Option(M.Sym×Bool). A caller-computed mutable x#y buffer and reserved fresh bank suffixes are given as the starting frame. One actual transition writes local boundary markers. Each following copy transition transfers the scanned input symbol to the child input bank with its true visited flag and simultaneously erases the source to false-tagged fresh blank. The child input head is physically rewound, then one actual halt step yields the exact tracked M.initCfg representation: input bank visited through the input length, all other banks visited only at their local marker, all child heads at their markers. Saved prefixes and root input/head are retained. The table contains no bank offsets, lengths, free marker writes or address oracle; producing the caller input and allocating fresh suffixes remain separate obligations.
-- source:
--   Original physical tracked-bank copy-and-erase preparation for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.TrackedBankPreparation

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

inductive State
  | mark | copy | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.mark,.copy,.rewind,.halt}
  complete := by intro q; cases q <;> simp

noncomputable def rawTransition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .mark => (.copy,fun i =>
      (if 1 ≤ i.val then some (M.startSym,true) else a i,
        if i.val = 1 ∨ i.val = 2 then .right else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.zero ∨
          TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.one ∨
          TrackedBankedSimulation.decode M (a ⟨1,by omega⟩) = M.sep then
        (.copy,fun i =>
          (if i.val = 1 then some (M.blank,false) else if i.val = 2 then
              some (TrackedBankedSimulation.decode M (a ⟨1,by omega⟩),true) else a i,
            if i.val = 1 ∨ i.val = 2 then .right else .stay))
      else (.rewind,fun i => (a i,if i.val = 2 then .left else .stay))
  | .rewind =>
      if a ⟨2,by have := M.two_le_k; omega⟩ = some (M.startSym,true) then
        (.halt,fun i => (a i,.stay))
      else (.rewind,fun i => (a i,if i.val = 2 then .left else .stay))
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
  cases q <;> simp only [rawTransition] <;> split_ifs <;> first | rfl | omega

/-- Physical tracked-bank initialization from a mutable caller input buffer.
All markers, flags, symbol transfers, source erasures and seeks are charged. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .mark
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

def inputWord (M : MultitapeTM) (x y : List Bool) : List M.Sym := x.map M.bitSym ++ M.sep :: y.map M.bitSym

def bankTape (M : MultitapeTM) (base : ℕ → Sym M) (offset : ℕ) (w : List M.Sym) (p : ℕ) : Sym M :=
  if p < offset then base p else some (M.tapeOf w (p - offset),decide (p - offset ≤ w.length))

def freshTape (M : MultitapeTM) (base : ℕ → Sym M) (offset p : ℕ) : Sym M :=
  if p < offset then base p else some (M.blank,false)

def sourceTape (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (p : ℕ) : Sym M :=
  if p < sigma then base p else if p = sigma then some (M.blank,false) else
    some (w.getD (p - sigma - 1) M.blank,decide (p - sigma - 1 < w.length))

def copyTape (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List M.Sym) (j p : ℕ) : Sym M :=
  if p < sigma then base p else if p = sigma then some (M.startSym,true)
    else if p < sigma + j + 1 then some (M.blank,false)
    else some (w.getD (p - sigma - 1) M.blank,decide (p - sigma - 1 < w.length))

def initialExtent (M : MultitapeTM) (x y : List Bool) : Fin M.k → ℕ :=
  fun j => if j = M.inTape then (inputWord M x y).length else 0

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) : (machine M).Cfg where
  state := .mark
  cells := fun i => if h : 2 ≤ i.val then freshTape M (base.cells i) (offset (innerTape M i h))
    else if i.val = 1 then sourceTape M (base.cells i) sigma (inputWord M x y) else base.cells i
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h)
    else if i.val = 1 then sigma else base.head i

noncomputable def copyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .copy
  cells := fun i => if h : 2 ≤ i.val then
    bankTape M (base.cells i) (offset (innerTape M i h)) (if i.val = 2 then (inputWord M x y).take j else [])
    else if i.val = 1 then copyTape M (base.cells i) sigma (inputWord M x y) j else base.cells i
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + (if i.val = 2 then j + 1 else 0)
    else if i.val = 1 then sigma + j + 1 else base.head i

noncomputable def callerBase (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (x y : List Bool) : (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i.val = 1 then bankTape M (base.cells i) sigma [] else base.cells i
  head := fun i => if i.val = 1 then sigma + (inputWord M x y).length + 1 else base.head i

noncomputable def readyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) : (machine M).Cfg where
  state := .halt
  cells := (TrackedBankedSimulation.embed M (callerBase M base sigma x y) offset (initialExtent M x y) (M.initCfg x y)).cells
  head := (TrackedBankedSimulation.embed M (callerBase M base sigma x y) offset (initialExtent M x y) (M.initCfg x y)).head

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (x y : List Bool) (p : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := (readyFrame M base sigma offset x y).cells
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + (if i.val = 2 then p else 0)
    else if i.val = 1 then sigma + (inputWord M x y).length + 1 else base.head i

end IntMul.TrackedBankPreparation


