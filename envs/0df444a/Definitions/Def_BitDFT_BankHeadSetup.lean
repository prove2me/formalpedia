-- Prove2me | Definitions.Def_BitDFT_BankHeadSetup
-- name    : BitDFT_BankHeadSetup
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:19:16.376853+00:00
-- url     : https://prove2.me/theorems/008619b1-4d43-4a3c-a445-224c5aaeb49f
-- title:
--   A one-transition controller for positioning reserved child-bank heads
-- statement:
--   For any machine alphabet and tape count, a fixed two-state controller moves each selected head at indices 2 through r+1 one cell right in one transition. It rewrites every scanned symbol unchanged and leaves both native heads parked. Its halt state freezes every tape.
-- source:
--   Charged physical head positioning before the tracked arbitrary-machine call.

import Definitions.Def_BitDFT_MachineSequence

namespace BitDFT.BankHeadSetup
open IntMul

def selected (r : ℕ) (i : ℕ) : Prop := 2 ≤ i ∧ i < r+2
instance (r i : ℕ) : Decidable (selected r i) := inferInstanceAs (Decidable (2 ≤ i ∧ i < r+2))

def transition (N : MultitapeTM) (r : ℕ) (q : Bool) (a : Fin N.k → N.Sym) :
    Bool × (Fin N.k → N.Sym × Move) :=
  (true,fun i => (a i,if q = false ∧ selected r i.val then .right else .stay))

def control (N : MultitapeTM) (r : ℕ) : MachineSequence.Controller N where
  K := Bool
  entry := false
  exit := true
  distinct := by decide
  transition := transition N r
  marker := by
    intro q a i hi
    constructor
    · exact hi
    · dsimp [transition]
      split <;> decide
  noMarker := by intro q a i hi; exact hi
  frozen := by intro a; simp [transition]
  readonly := by intro q a; rfl

abbrev machine (N : MultitapeTM) (r : ℕ) := (control N r).machine

def start (N : MultitapeTM) (r : ℕ) (base : N.Cfg) : (machine N r).Cfg :=
  ⟨false,base.cells,base.head⟩

def finish (N : MultitapeTM) (r : ℕ) (base : N.Cfg) : (machine N r).Cfg :=
  ⟨true,base.cells,fun i => if selected r i.val then base.head i+1 else base.head i⟩

end BitDFT.BankHeadSetup


