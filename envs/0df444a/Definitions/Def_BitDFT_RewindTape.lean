-- Prove2me | Definitions.Def_BitDFT_RewindTape
-- name    : BitDFT_RewindTape
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:09:15.308718+00:00
-- url     : https://prove2.me/theorems/f3498e6e-a5e3-4cee-bf26-da7f1b444f3a
-- title:
--   Rewind one selected tape to its first data cell with an exact clock — machine
-- statement:
--   For an arbitrary finite multitape machine alphabet and a selected tape, assume the tape has its start marker exactly at position zero. From head position p, the rewind controller halts at position one in exactly p+1 transitions. All tape contents and all other heads are preserved. The initial head position is part of the full specified configuration.
-- source:
--   Charged setup for the exact output scaler in the finite-precision DFT transfer mission.

import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.RewindTape
open IntMul MachineSequence

def transition (N : MultitapeTM) (j : Fin N.k) (q : Bool) (a : Fin N.k → N.Sym) :
    Bool × (Fin N.k → N.Sym × Move) := by
  classical
  exact (q || decide (a j = N.startSym), fun i => (a i,
    if q then .stay else if i = j then
      if a j = N.startSym then .right else .left else .stay))

def control (N : MultitapeTM) (j : Fin N.k) : Controller N where
  K := Bool
  entry := false
  exit := true
  distinct := by decide
  transition := transition N j
  marker := by
    intro q a i hi
    constructor
    · exact hi
    · dsimp [transition]
      by_cases hq : q = true
      · simp [hq]
      · have hq' : q = false := by cases q <;> simp_all
        by_cases hij : i = j
        · subst i; simp [hq',hi]
        · simp [hq',hij]
  noMarker := by intro q a i hi; exact hi
  frozen := by intro a; simp [transition]
  readonly := by intro q a; rfl

abbrev machine (N : MultitapeTM) (j : Fin N.k) := (control N j).machine

def frame (N : MultitapeTM) (j : Fin N.k) (base : N.Cfg) (q : Bool) (p : ℕ) :
    (machine N j).Cfg := ⟨q,base.cells,Function.update base.head j p⟩

end BitDFT.RewindTape


