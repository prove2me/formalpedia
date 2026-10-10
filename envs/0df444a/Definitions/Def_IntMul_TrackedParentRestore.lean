-- Prove2me | Definitions.Def_IntMul_TrackedParentRestore
-- name    : IntMul_TrackedParentRestore
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:32:04.488025+00:00
-- url     : https://prove2.me/theorems/29003acf-5e44-463c-8aec-ecde427ab7d6
-- title:
--   Physical independent restoration of parent heads to retained local markers
-- statement:
--   Two finite states on the same M.k+2 tapes and Option(M.Sym×Bool) alphabet restore parent work heads by physical left moves. Each work head still away from its retained parent marker moves left; each already on its marker stays. When all work heads scan their parent markers, one actual halt transition completes restoration. All bank cells and visited flags, root input and caller output are retained, and root/buffer heads stay fixed. A tracked parent frame and unique local marker on every parent bank ensure no premature stop. The proof-side starting displacement pos_j and bank offsets never enter the transition table. This routine is intended to follow complete child cleanup, which removes child markers before restoration.
-- source:
--   Original physical tracked parent-head restoration for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.TrackedParentRestore

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.BankedSimulation (workTape innerTape)

inductive State
  | rewind | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.halt}
  complete := by intro q; cases q <;> simp

noncomputable def rawTransition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .rewind =>
      if ∀ j : Fin M.k, a (workTape M j) = some (M.startSym,true) then
        (.halt,fun i => (a i,.stay))
      else (.rewind,fun i => (a i,if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) :=
  let r := rawTransition M q a
  (r.1,fun i => TrackedBankCleanup.protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem input_raw (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    ((rawTransition M q a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  cases q with
  | halt => rfl
  | rewind => dsimp only [rawTransition]; split <;> rfl

/-- Two finite states physically restore each parent head to its nearest
retained local marker. Cleared child suffixes contain no intervening local
marker. Root, buffer and every bank cell are retained throughout. -/
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
  halt_fixed := by intro a; simp [transition,rawTransition,protect_stay]
  input_readonly := by
    intro q a
    change (TrackedBankCleanup.protect M (a ⟨0,by omega⟩)
      ((rawTransition M q a).2 ⟨0,by omega⟩).1 _).1 = _
    rw [input_raw]
    cases a ⟨0,by omega⟩ <;> rfl

noncomputable def parentBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := base.cells
  head := base.head

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) : (machine M).Cfg where
  state := .rewind
  cells := (TrackedBankedSimulation.embed M (parentBase M base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then
    offset (innerTape M i h) + (pos (innerTape M i h) - r)
    else base.head i

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) : (machine M).Cfg :=
  rewindFrame M base offset extent c pos 0

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg where
  state := .halt
  cells := (TrackedBankedSimulation.embed M (parentBase M base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) else base.head i

end IntMul.TrackedParentRestore


