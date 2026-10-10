-- Prove2me | Definitions.Def_IntMul_TrackedSelectiveParentRestore
-- name    : IntMul_TrackedSelectiveParentRestore
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T03:12:46.425606+00:00
-- url     : https://prove2.me/theorems/3e826e0c-2b3e-4612-bb33-341272c9d373
-- title:
--   Physical selective parent-bank restoration with fixed finite tape selection
-- statement:
--   A deterministic two-state physical restoration service on the same fixed k+2 tapes and visited-bit alphabet as the tracked bank services. A finite selection of work-bank heads is compiled into its transition table. It rewinds each selected head until it sees its nearest retained local parent marker, while unselected heads, the root input and the shared buffer remain still. Every tape cell is preserved. The selected maximum relative starting position is proof data used to describe and bound the run; no position, offset, extent or recursion depth enters the finite transition function. Selecting only the parent result tape avoids rewinding large unaffected parent banks.
-- source:
--   Original selective physical parent restoration for fast recursive integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.TrackedSelectiveParentRestore

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankCleanup (span)

inductive State
  | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.halt}
  complete := by intro q; cases q <;> simp

/-- A compile-time finite selection of bank heads. Unselected heads never
move. Positions and bank boundaries are not inputs to the transition. -/
noncomputable def rawTransition (M : MultitapeTM) (active : Fin M.k → Bool)
    (q : State) (a : Fin (M.k+2) → Sym M) :
    State × (Fin (M.k+2) → Sym M × Move) := by
  classical
  exact match q with
  | .rewind =>
      if ∀ j : Fin M.k, active j=true → a (workTape M j)=some (M.startSym,true) then
        (.halt,fun i => (a i,.stay))
      else (.rewind,fun i => (a i,
        if h : 2 ≤ i.val then
          if active (innerTape M i h)=true ∧ a i≠some (M.startSym,true) then .left else .stay
        else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (active : Fin M.k → Bool)
    (q : State) (a : Fin (M.k+2) → Sym M) :
    State × (Fin (M.k+2) → Sym M × Move) :=
  let r := rawTransition M active q a
  (r.1,fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay=(a,.stay) := by cases a <;> rfl

private theorem input_raw (M : MultitapeTM) (active : Fin M.k → Bool)
    (q : State) (a : Fin (M.k+2) → Sym M) :
    ((rawTransition M active q a).2 ⟨0,by omega⟩).1=a ⟨0,by omega⟩ := by
  cases q with
  | halt => rfl
  | rewind => dsimp only [rawTransition]; split <;> rfl

/-- One fixed finite two-state machine selectively restores parent markers
while preserving every cell and every unselected head. It uses the same
visited-bit alphabet and the same k+2 physical tapes as the other services. -/
noncomputable abbrev machine (M : MultitapeTM) (active : Fin M.k → Bool) : MultitapeTM where
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
  k := M.k+2
  two_le_k := by omega
  δ := transition M active
  start_preserved := by
    classical
    intro q a i hi
    change (TrackedBankCleanup.protect M (a i) _ _).1=none ∧
      (TrackedBankCleanup.protect M (a i) _ _).2≠.left
    rw [hi]
    simp only [TrackedBankCleanup.protect]
    split <;> simp_all
  start_only_at_start := by
    classical
    intro q a i hi
    change (TrackedBankCleanup.protect M (a i) _ _).1≠none
    cases hs : a i with
    | none => exact False.elim (hi hs)
    | some s => simp only [TrackedBankCleanup.protect]; split <;> simp
  halt_fixed := by intro a; simp [transition,rawTransition,protect_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M active q a).2 ⟨0,by omega⟩).1 _).1=_
    rw [input_raw]
    cases a ⟨0,by omega⟩ <;> rfl

noncomputable def parentBase (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) : (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := base.cells
  head := base.head

noncomputable def selectedSpan (M : MultitapeTM) (active : Fin M.k → Bool)
    (pos : Fin M.k → ℕ) : ℕ := span M (fun j => if active j=true then pos j else 0)

noncomputable def rewindFrame (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) : (machine M active).Cfg where
  state := .rewind
  cells := (TrackedBankedSimulation.embed M (parentBase M active base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then
    let j := innerTape M i h
    offset j+(if active j=true then pos j-r else pos j)
    else base.head i

noncomputable def initialFrame (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) : (machine M active).Cfg :=
  rewindFrame M active base offset extent c pos 0

noncomputable def finalFrame (M : MultitapeTM) (active : Fin M.k → Bool)
    (base : (machine M active).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (pos : Fin M.k → ℕ) : (machine M active).Cfg where
  state := .halt
  cells := (TrackedBankedSimulation.embed M (parentBase M active base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then
    let j := innerTape M i h
    offset j+(if active j=true then 0 else pos j)
    else base.head i

end IntMul.TrackedSelectiveParentRestore


