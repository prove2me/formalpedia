-- Prove2me | Definitions.Def_OnlineScratchWindow
-- name    : OnlineScratchWindow
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T03:52:35.033521+00:00
-- url     : https://prove2.me/theorems/4503e567-815a-5530-99cf-a0e5a6687ed8
-- title:
--   Finite local programs for a movable product-tape scratch window
-- statement:
--   On a single tape, the first track stores the consumer data and the second holds a width-w frame between two markers. Local finite-control programs move this frame one cell left or right while preserving the entire consumer track.
-- source:
--   Movable finite scratch buffer for composing a streaming transducer with an online one-tape machine.

import Definitions.Def_SingleTapeWorkBoundary

set_option autoImplicit false

namespace PvsNP.OnlineWindowShift

open PvsNP.WorkBoundarySplice

/-- The movable track has two boundary markers, ordinary payload symbols,
and a distinguished symbol outside the frame. -/
inductive Cell (P : Type)
  | blank | near | far | data (symbol : P)
  deriving Fintype, DecidableEq

/-- During a right shift the only payload in the control is a single cell. -/
inductive Phase (P : Type)
  | enter | carry (symbol : Cell P) | deposit | returnHome | done
  deriving Fintype, DecidableEq

variable {P C : Type}

def command : Phase P → Cell P → Option (Phase P × Cell P × Motion)
  | .enter, .near => some (.carry .near,.blank,.right)
  | .carry saved, .data x => some (.carry (.data x),saved,.right)
  | .carry saved, .far => some (.deposit,saved,.right)
  | .deposit, .blank => some (.returnHome,.far,.left)
  | .returnHome, .far => some (.returnHome,.far,.left)
  | .returnHome, .data x => some (.returnHome,.data x,.left)
  | .returnHome, .near => some (.done,.near,.stay)
  | _, _ => none

def shiftRightMachine : Machine (Phase P) (C × Cell P) :=
  fun mode square => (command mode square.2).map fun (next,symbol,move) =>
    (next,(square.1,symbol),move)

/-- The frame has its near marker at p and exactly w payload cells. The
payload function is read only at indices 0 through w-1. -/
def frame (p : ℤ) (w : ℕ) (payload : ℕ → P) (i : ℤ) : Cell P :=
  if i = p then .near
  else if i = p+(w : ℤ)+1 then .far
  else if p < i ∧ i < p+(w : ℤ)+1 then .data (payload (i-p-1).toNat)
  else .blank

def tracks (consumer : ℤ → C) (scratch : ℤ → Cell P) : ℤ → (C × Cell P) :=
  fun i => (consumer i,scratch i)

/-- The left shift first seeks the far marker, shifts from that marker,
then seeks the new near marker. -/
inductive LeftPass
  | seekFar | shift | seekNear
  deriving DecidableEq

instance : Fintype LeftPass where
  elems := {.seekFar,.shift,.seekNear}
  complete pass := by cases pass <;> simp

inductive LeftPhase (P : Type)
  | active (pass : LeftPass) (phase : Phase P)
  | done
  deriving Fintype, DecidableEq

def LeftPass.mirrored : LeftPass → Bool
  | .seekFar | .shift => true
  | .seekNear => false

def leftPhase (pass : LeftPass) (mode : Phase P) : LeftPhase P :=
  match mode with
  | .done => match pass with
    | .seekFar => .active .shift .enter
    | .shift => .active .seekNear .returnHome
    | .seekNear => .done
  | _ => .active pass mode

def flipPos (mirror : Bool) (z : ℤ) : ℤ :=
  if mirror then -z else z

def flipCell (mirror : Bool) (cell : Cell P) : Cell P :=
  if mirror then
    match cell with
    | .near => .far
    | .far => .near
    | _ => cell
  else cell

def flipSquare (mirror : Bool) (cell : C × Cell P) : C × Cell P :=
  (cell.1,flipCell mirror cell.2)

def flipMotion (mirror : Bool) (motion : Motion) : Motion :=
  if mirror then
    match motion with
    | .left => .right
    | .right => .left
    | .stay => .stay
  else motion

def shiftLeftMachine : Machine (LeftPhase P) (C × Cell P)
  | .done, _ => none
  | .active pass mode, square =>
    (shiftRightMachine mode (flipSquare pass.mirrored square)).map fun (next,out,motion) =>
      (leftPhase pass next,flipSquare pass.mirrored out,flipMotion pass.mirrored motion)

end PvsNP.OnlineWindowShift


