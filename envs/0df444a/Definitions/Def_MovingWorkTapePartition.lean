-- Prove2me | Definitions.Def_MovingWorkTapePartition
-- name    : MovingWorkTapePartition
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T03:23:22.363716+00:00
-- url     : https://prove2.me/theorems/162824f6-94a7-4b79-a8d4-55e0e0b2ede2
-- title:
--   Moving partitions of a single work tape and their time-stamped records
-- statement:
--   At each clock, take each work cell from its designated owner. Record synchronized control and head addresses when a head changes sides of a moving cut, and record the post-step values of cells transferred by the cut.
-- source:
--   Time-synchronized extension of Hennie single-tape crossing records, doi:10.1016/S0019-9958(65)90399-2.

import Definitions.Def_SingleTapeWorkBoundary

set_option autoImplicit false

namespace PvsNP.MovingWorkBoundary

open PvsNP.WorkBoundarySplice Function

variable {I Q Γ : Type}

/-- A halted source retains its final configuration at later clocks. -/
def tick (M : Machine Q Γ) (c : Config Q Γ) : Config Q Γ :=
  (step M c).getD c

/-- Choose each cell from its owner and the head and control from the
currently active run. An ownership map may describe more than two regions. -/
def assemble (owner : ℤ → I) (active : I) (runs : I → Config Q Γ) : Config Q Γ :=
  ⟨(runs active).state,(runs active).head,fun i => (runs (owner i)).tape i⟩

def trace (M : Machine Q Γ) (start : Config Q Γ) (t : ℕ) : Config Q Γ :=
  (tick M)^[t] start

def sideAt (cut : ℕ → ℤ) (M : Machine Q Γ) (start : Config Q Γ) (t : ℕ) : Bool :=
  rightOf (cut t) (trace M start t).head

/-- A timed control message is present precisely when the head and the cut
end the step on opposite relative sides from where they started. -/
def controlAt (cut : ℕ → ℤ) (M : Machine Q Γ) (start : Config Q Γ) (t : ℕ) : Option (Q × ℤ) :=
  if sideAt cut M start t = sideAt cut M start (t+1) then none
  else some ((trace M start (t+1)).state,(trace M start (t+1)).head)

/-- A moving cut records the post-step contents of the cells whose ownership
changes. The handoff positions are determined by the common schedule. -/
def cellAt (cut : ℕ → ℤ) (M : Machine Q Γ) (start : Config Q Γ) (t : ℕ) (i : ℤ) : Option Γ :=
  if rightOf (cut t) i = rightOf (cut (t+1)) i then none
  else some ((trace M start (t+1)).tape i)

def pair (left right : Config Q Γ) : Bool → Config Q Γ
  | false => left
  | true => right

end PvsNP.MovingWorkBoundary


