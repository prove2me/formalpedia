-- Prove2me | Definitions.Def_SingleTapeWorkBoundary
-- name    : SingleTapeWorkBoundary
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-27T03:04:23.079429+00:00
-- url     : https://prove2.me/theorems/ee58794b-15d6-55c5-9530-646849d4da3d
-- title:
--   Work-tape boundaries and finite crossing records for a local tape machine
-- statement:
--   A local single-tape machine has a control state, an integer head position, and a tape function on integer addresses. Its transition reads and writes the head position and moves at most one cell. A boundary record stores the control states just after each crossing. Patching a tape takes the two half-tapes from the two specified owners.
-- source:
--   F. C. Hennie, One-tape, off-line Turing machine computations (1965), Section II, doi:10.1016/S0019-9958(65)90399-2.

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PvsNP.WorkBoundarySplice

/-- A local one-tape move has unit displacement. -/
inductive Motion
  | left
  | stay
  | right

def Motion.shift : Motion → ℤ → ℤ
  | .left, h => h - 1
  | .stay, h => h
  | .right, h => h + 1

structure Config (Q Γ : Type*) where
  state : Q
  head : ℤ
  tape : ℤ → Γ

abbrev Machine (Q Γ : Type*) := Q → Γ → Option (Q × Γ × Motion)

variable {Q Γ : Type*}

def write (tape : ℤ → Γ) (head : ℤ) (value : Γ) (cell : ℤ) : Γ :=
  if cell = head then value else tape cell

def step (M : Machine Q Γ) (c : Config Q Γ) : Option (Config Q Γ) :=
  (M c.state (c.tape c.head)).map fun (q, a, move) =>
    ⟨q, move.shift c.head, write c.tape c.head a⟩

def rightOf (cut i : ℤ) : Bool := decide (cut < i)

/-- The control and head belong to the active owner. Each half-tape is taken
from its assigned source, including cells that were never visited. -/
def patch (cut : ℤ) (ownsRight : Bool) (owner other : Config Q Γ) : Config Q Γ :=
  ⟨owner.state, owner.head, fun i =>
    if rightOf cut i = ownsRight then owner.tape i else other.tape i⟩

/-- A finite segment which never crosses the cut. -/
inductive Stays (M : Machine Q Γ) (cut : ℤ) :
    Config Q Γ → Config Q Γ → ℕ → Prop
  | refl (a : Config Q Γ) : Stays M cut a a 0
  | next {a b c : Config Q Γ} {n : ℕ} :
      step M a = some b → rightOf cut b.head = rightOf cut a.head →
      Stays M cut b c n → Stays M cut a c (n+1)

def Exits (M : Machine Q Γ) (cut : ℤ)
    (a b : Config Q Γ) (n : ℕ) : Prop :=
  ∃ p : Config Q Γ, ∃ m : ℕ, n = m+1 ∧ Stays M cut a p m ∧
    step M p = some b ∧ rightOf cut b.head ≠ rightOf cut p.head

/-- An accepting tape computation recording just the successive arrival
control states at the fixed work-tape edge. -/
inductive Run (M : Machine Q Γ) (cut : ℤ) (accept : Q → Prop) :
    Config Q Γ → List Q → ℕ → Prop
  | finish {a b : Config Q Γ} {n : ℕ} :
      Stays M cut a b n → accept b.state → Run M cut accept a [] n
  | cross {a b : Config Q Γ} {n m : ℕ} {q : Q} {record : List Q} :
      b.state = q → Exits M cut a b n → Run M cut accept b record m →
      Run M cut accept a (q::record) (n+m)

end PvsNP.WorkBoundarySplice


