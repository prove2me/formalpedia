-- Prove2me | Definitions.Def_IntMul_TrackedBankReservation
-- name    : IntMul_TrackedBankReservation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T23:25:30.093259+00:00
-- url     : https://prove2.me/theorems/7cb93428-d1f1-4876-be58-91687c53bfa4
-- title:
--   Physical independent reservation of fresh suffixes after tracked parent banks
-- statement:
--   Two finite states on the same M.k+2 tapes and Option(M.Sym×Bool) alphabet physically seek to the first unvisited cell of every tracked parent bank. Each still-visited work head moves right one actual cell per transition; finished heads stay. When all work heads scan unvisited cells, one real halt transition completes reservation. All cells, flags, root input and caller buffer are unchanged, and root/buffer heads stay fixed. From parent extent E_j and relative head pos_j at most E_j+1, the proof-side new child boundary is oldOffset_j+E_j+1. Neither offsets nor extents enter delta; the finite scanned flag alone controls each head. Blank-tail initialization certifies the entire suffix at each physically found boundary is fresh. Marker creation and child input generation are later charged phases.
-- source:
--   Original physical tracked fresh-suffix reservation for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankCleanup

namespace IntMul.TrackedBankReservation

open IntMul.TrackedBankedSimulation (Sym)
open IntMul.BankedSimulation (workTape innerTape)

inductive State
  | seek | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.seek,.halt}
  complete := by intro q; cases q <;> simp

/-- Global markers count as occupied. All tracked cells expose one finite
visited flag; no head address or history is an input to the transition. -/
def visited (M : MultitapeTM) : Sym M → Bool
  | none => true
  | some s => s.2

noncomputable def transition (M : MultitapeTM) (q : State)
    (a : Fin (M.k + 2) → Sym M) : State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .seek =>
      if ∀ j : Fin M.k, visited M (a (workTape M j)) = false then
        (.halt,fun i => (a i,.stay))
      else (.seek,fun i => (a i,if 2 ≤ i.val ∧ visited M (a i) = true then .right else .stay))
  | .halt => (.halt,fun i => (a i,.stay))

/-- Two finite states physically find a fresh suffix on every child bank,
independently stopping each head at its first unvisited cell. All root,
buffer and bank cells are retained; root and buffer heads stay fixed. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .seek
  qHalt := .halt
  start_ne_halt := by decide
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | halt =>
        constructor
        · exact hi
        · change Move.stay ≠ Move.left
          decide
    | seek =>
        dsimp only [transition]
        split
        · constructor
          · exact hi
          · change Move.stay ≠ Move.left
            decide
        · constructor
          · exact hi
          · change (if 2 ≤ i.val ∧ visited M (a i) = true then Move.right else Move.stay) ≠ Move.left
            split
            · change Move.right ≠ Move.left
              decide
            · change Move.stay ≠ Move.left
              decide
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | halt => exact hi
    | seek => simp only [transition]; split_ifs <;> exact hi
  halt_fixed := by intro a; rfl
  input_readonly := by
    classical
    intro q a
    cases q with
    | halt => rfl
    | seek => simp only [transition]; split_ifs <;> rfl

def distance (M : MultitapeTM) (extent pos : Fin M.k → ℕ) : Fin M.k → ℕ :=
  fun j => extent j + 1 - pos j

def newOffsets (M : MultitapeTM) (offset extent : Fin M.k → ℕ) : Fin M.k → ℕ :=
  fun j => offset j + extent j + 1

noncomputable def parentBase (M : MultitapeTM) (base : (machine M).Cfg) :
    (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := base.cells
  head := base.head

noncomputable def seekFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) (r : ℕ) : (machine M).Cfg where
  state := .seek
  cells := (TrackedBankedSimulation.embed M (parentBase M base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then
    offset (innerTape M i h) + pos (innerTape M i h) + min r (distance M extent pos (innerTape M i h))
    else base.head i

noncomputable def initialFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg :=
  seekFrame M base offset extent c c.head 0

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg where
  state := .halt
  cells := (TrackedBankedSimulation.embed M (parentBase M base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then newOffsets M offset extent (innerTape M i h) else base.head i

end IntMul.TrackedBankReservation


