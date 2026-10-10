-- Prove2me | Definitions.Def_IntMul_TrackedRootInputCopy
-- name    : IntMul_TrackedRootInputCopy
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:00:00.185852+00:00
-- url     : https://prove2.me/theorems/f960d7e1-f211-42cf-9f6a-cd57462c3c0f
-- title:
--   Physical read-only native input copy into a mutable tracked caller buffer
-- statement:
--   Five fixed finite states on the shared M.k+2 tapes and Option(M.Sym×Bool) alphabet copy the real native x#y input into mutable output-buffer cells starting at two, reserving blank cell one for later child-bank preparation. Every global marker is preserved. Every work head is physically moved from global cell zero to fresh cell one and stays there. The root input is read-only. Scanned finite input symbols control copying; no input length or head address enters delta. On the real input-end blank the buffer head physically rewinds to its existing global marker and moves right to the reserved boundary. The copied buffer and all head positions are given by full frames; no fresh input or markers are assumed.
-- source:
--   Original physical native root-input bridge for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankPreparation

namespace IntMul.TrackedRootInputCopy

open IntMul.TrackedBankedSimulation (Sym)

inductive State
  | start | gap | copy | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.start,.gap,.copy,.rewind,.halt}
  complete := by intro q; cases q <;> simp

noncomputable def rawTransition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .start => (.gap,fun i => (a i,.right))
  | .gap => (.copy,fun i => (a i,if i.val = 1 then .right else .stay))
  | .copy =>
      if TrackedBankedSimulation.decode M (a ⟨0,by omega⟩) = M.zero ∨
          TrackedBankedSimulation.decode M (a ⟨0,by omega⟩) = M.one ∨
          TrackedBankedSimulation.decode M (a ⟨0,by omega⟩) = M.sep then
        (.copy,fun i =>
          (if i.val = 1 then some (TrackedBankedSimulation.decode M (a ⟨0,by omega⟩),true) else a i,
            if i.val = 0 ∨ i.val = 1 then .right else .stay))
      else (.rewind,fun i => (a i,if i.val = 1 then .left else .stay))
  | .rewind =>
      if a ⟨1,by omega⟩ = none then
        (.halt,fun i => (a i,if i.val = 1 then .right else .stay))
      else (.rewind,fun i => (a i,if i.val = 1 then .left else .stay))
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

/-- Physical native-input copy to a mutable buffer with one reserved blank
cell after the global marker; every work head is parked at fresh cell one. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .start
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

noncomputable def gapFrame (M : MultitapeTM) (x y : List Bool) : (machine M).Cfg where
  state := .gap
  cells := ((machine M).initCfg x y).cells
  head := fun _ => 1

noncomputable def copyFrame (M : MultitapeTM) (x y : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .copy
  cells := fun i => if i.val = 1 then
    TrackedBankPreparation.sourceTape M (((machine M).initCfg x y).cells i) 1
      ((TrackedBankPreparation.inputWord M x y).take j)
    else ((machine M).initCfg x y).cells i
  head := fun i => if i.val = 0 then j + 1 else if i.val = 1 then j + 2 else 1

noncomputable def rewindFrame (M : MultitapeTM) (x y : List Bool) (p : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := (copyFrame M x y (TrackedBankPreparation.inputWord M x y).length).cells
  head := fun i => if i.val = 0 then (TrackedBankPreparation.inputWord M x y).length + 1
    else if i.val = 1 then p else 1

noncomputable def finalFrame (M : MultitapeTM) (x y : List Bool) : (machine M).Cfg where
  state := .halt
  cells := (copyFrame M x y (TrackedBankPreparation.inputWord M x y).length).cells
  head := fun i => if i.val = 0 then (TrackedBankPreparation.inputWord M x y).length + 1 else 1

end IntMul.TrackedRootInputCopy


