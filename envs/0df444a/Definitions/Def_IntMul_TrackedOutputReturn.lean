-- Prove2me | Definitions.Def_IntMul_TrackedOutputReturn
-- name    : IntMul_TrackedOutputReturn
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T22:23:39.829758+00:00
-- url     : https://prove2.me/theorems/6b119cf7-a66b-4388-bc9c-542d8a1c1cf8
-- title:
--   Physical output return preserving complete tracked child workspace
-- statement:
--   For each finite child machine M, a fixed M.k+2-tape three-state output-return machine over Option(M.Sym×Bool). A prepared empty caller buffer and the child's output bank have local tagged markers. Both heads rewind independently, waiting at their own markers until both arrive. One transition moves them onto payloads, then each child output bit is physically copied into the caller buffer. Every child-bank cell and its visited flag remain unchanged. The root input and all ancestor prefixes are preserved. Copying stops at the canonical child's first blank, followed by a real halt transition. Offsets, distances, words and visited extents occur only in proof-side frames; the finite table reads only state and scanned symbols. Initial local markers and empty buffer preparation remain separate charged obligations.
-- source:
--   Original physical tracked output-return construction for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.TrackedOutputReturn

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

inductive State
  | rewind | copy | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.copy,.halt}
  complete := by intro q; cases q <;> simp

noncomputable def rawTransition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .rewind =>
      if a ⟨1,by omega⟩ = some (M.startSym,true) ∧
          a ⟨3,by have := M.two_le_k; omega⟩ = some (M.startSym,true) then
        (.copy,fun i => (a i,if i.val = 1 ∨ i.val = 3 then .right else .stay))
      else (.rewind,fun i => (a i,
        if (i.val = 1 ∨ i.val = 3) ∧ a i ≠ some (M.startSym,true) then .left else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a ⟨3,by have := M.two_le_k; omega⟩) = M.zero ∨
          TrackedBankedSimulation.decode M (a ⟨3,by have := M.two_le_k; omega⟩) = M.one then
        (.copy,fun i =>
          (if i.val = 1 then some (TrackedBankedSimulation.decode M
            (a ⟨3,by have := M.two_le_k; omega⟩),true) else a i,
            if i.val = 1 ∨ i.val = 3 then .right else .stay))
      else (.halt,fun i => (a i,.stay))
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

/-- A fixed physical output-return routine over the tracked-bank alphabet.
Both heads seek their own markers, then copy child bits while retaining flags. -/
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
  halt_fixed := by
    intro a
    simp [transition,rawTransition,protect_self_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M q a).2 ⟨0,by omega⟩).1 _).1 = _
    rw [raw_input_readonly]
    cases a ⟨0,by omega⟩ <;> rfl

/-- The returned word is stored in a mutable interior buffer with a saved
prefix, a tagged local marker, tagged bits and a fresh blank tail. -/
def bufferTape (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) (p : ℕ) : Sym M :=
  if p < sigma then base p else if p = sigma then some (M.startSym,true) else
    some ((w.map M.bitSym).getD (p - sigma - 1) M.blank,decide (p - sigma - 1 < w.length))

noncomputable def callerBase (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) : (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := fun i => if i.val = 1 then bufferTape M (base.cells i) sigma [] else base.cells i
  head := fun i => if i.val = 1 then sigma + a else base.head i

noncomputable def returnFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (a b : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := (TrackedBankedSimulation.embed M (callerBase M base sigma a) offset extent c).cells
  head := fun i => if i.val = 1 then sigma + a else if i.val = 3 then offset M.outTape + b
    else (TrackedBankedSimulation.embed M (callerBase M base sigma a) offset extent c).head i

noncomputable def copyFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .copy
  cells := fun i => if i.val = 1 then bufferTape M (base.cells i) sigma (w.take j)
    else (TrackedBankedSimulation.embed M (callerBase M base sigma 0) offset extent c).cells i
  head := fun i => if i.val = 1 then sigma + j + 1 else if i.val = 3 then offset M.outTape + j + 1
    else (TrackedBankedSimulation.embed M (callerBase M base sigma 0) offset extent c).head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) : (machine M).Cfg where
  state := .halt
  cells := (copyFrame M base sigma offset extent c w w.length).cells
  head := (copyFrame M base sigma offset extent c w w.length).head

end IntMul.TrackedOutputReturn


