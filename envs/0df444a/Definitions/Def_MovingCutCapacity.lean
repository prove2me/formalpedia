-- Prove2me | Definitions.Def_MovingCutCapacity
-- name    : MovingCutCapacity
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T03:30:34.701668+00:00
-- url     : https://prove2.me/theorems/ebaa82e0-5258-4141-868a-02d1afad8a2b
-- title:
--   Finite timed control and tape-transfer codes for unit-speed cuts
-- statement:
--   A moving-cut transcript includes the initial head side, a bounded list of time-stamped control transfers, and the symbol transferred at each cut move. A control transfer carries the new state and one of four relative head offsets. The public cut schedule determines the tape handoff addresses.
-- source:
--   Finite coding of a synchronized moving tape boundary.

import Definitions.Def_MovingWorkTapePartition

set_option autoImplicit false

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice Function

variable {Q Γ : Type}

def UnitCut (cut : ℕ → ℤ) (T : ℕ) : Prop :=
  ∀ t < T, cut t-1 ≤ cut (t+1) ∧ cut (t+1) ≤ cut t+1

def headOffset (cut h : ℤ) : Fin 4 := ⟨(h-cut+1).toNat%4,Nat.mod_lt _ (by decide)⟩

def controlCode (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ) (t : ℕ) :
    Option (Q × Fin 4) :=
  (controlAt cut M a t).map fun qh => (qh.1,headOffset (cut (t+1)) qh.2)

abbrev MoveTime (cut : ℕ → ℤ) (T : ℕ) :=
  {t : Fin T // cut t.val ≠ cut (t.val+1)}

def handoffCode (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ) (T : ℕ)
    (t : MoveTime cut T) : Γ :=
  (trace M a (t.val.val+1)).tape (max (cut t.val.val) (cut (t.val.val+1)))

abbrev TimedEvent (Q : Type) (T : ℕ) := Fin T × (Q × Fin 4)

def timedEvents (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ) (T : ℕ) :
    List (TimedEvent Q T) := (List.finRange T).filterMap fun t =>
  (controlCode cut M a t.val).map fun q => (t,q)

/-- The positions of all tape handoffs are public. Only their symbols are
recorded, with one slot per time at which the unit-speed cut moves. -/
abbrev Signature (cut : ℕ → ℤ) (T r : ℕ) (Q Γ : Type) :=
  Bool × (Fin r → Option (TimedEvent Q T)) × (MoveTime cut T → Γ)

def signature (cut : ℕ → ℤ) (M : Machine Q Γ) (a : Config Q Γ) (T r : ℕ) :
    Signature cut T r Q Γ :=
  ⟨sideAt cut M a 0,fun i => (timedEvents cut M a T)[i.val]?,handoffCode cut M a T⟩

noncomputable def cutCapacity (cut : ℕ → ℤ) (T r : ℕ) (Q Γ : Type) [Fintype Q] [Fintype Γ] : ℕ :=
  2*(T*(Fintype.card Q*4)+1)^r*(Fintype.card Γ)^(Fintype.card (MoveTime cut T))

end PvsNP.MovingWorkBoundary


