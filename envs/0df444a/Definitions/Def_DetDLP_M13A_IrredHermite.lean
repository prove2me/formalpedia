-- Prove2me | Definitions.Def_DetDLP_M13A_IrredHermite
-- name    : DetDLP_M13A_IrredHermite
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T01:32:14.134276+00:00
-- url     : https://prove2.me/theorems/5a7940db-55f8-49b6-bf71-30065f83f866
-- title:
--   Unary-budgeted binary polynomial search and Newton inverse rounds
-- statement:
--   Boolean coefficient words are stored most significant coefficient first. Monic long division and a unary-budgeted search enumerate potential divisors of degree at most half the target degree. A separate arithmetic step performs modular Newton iteration.

import Mathlib

set_option autoImplicit false
namespace DetDLP_M13A_IrredHermite
open Polynomial

/-- Coefficients in descending degree, including the leading bit. -/
noncomputable def polynomial (R : Type*) [Semiring R] : List Bool → R[X]
  | [] => 0
  | b :: bs => C (b.toNat : R) * X ^ bs.length + polynomial R bs

/-- One monic long-division step. The divisor's leading one is implicit. -/
def divStep (g r : List Bool) : List Bool :=
  if g.length < r.length then
    if r.headD false then
      ((g.zip r.tail).map (fun p => p.1 ^^ p.2)) ++ r.tail.drop g.length
    else r.tail
  else r

def remainder (g f : List Bool) : List Bool :=
  f.foldl (fun r _ => divStep g r) f

def word (positions : List ℕ) (mask : ℕ) : List Bool :=
  positions.map (fun j => mask.testBit j)

def capacity (positions : List ℕ) : ℕ :=
  ((positions.map (fun _ => false)) ++ [true]).foldr Nat.bit 0

def candidates (positions masks : List ℕ) : List (List Bool) :=
  (masks.take (capacity positions)).map (fun mask => word positions mask)

def passes (positions masks : List ℕ) (f : List Bool) : Bool :=
  positions.all fun d =>
    !(0 < d && d + d ≤ positions.length) ||
      (candidates (positions.take d) masks).all fun g => (remainder g f).any id

def search (positions masks : List ℕ) : List Bool :=
  (((candidates positions masks).map (true :: ·)).find? (passes positions masks)).getD []

def findIrredPoly (κ : ℕ) : List Bool :=
  search (List.range κ) (List.range (2 ^ κ))

/-- Its length is the unary budget; its true-bit count is the degree. -/
def irredMachine (w : List Bool) : List Bool :=
  search (List.range (w.filter id).length) (List.range w.length)

def inverseStep (m x y : ℕ) : ℕ := (y * (m + 2 - x * y % m)) % m

def inverseRounds (fuel : List Bool) (m x : ℕ) : ℕ :=
  fuel.foldl (fun y _ => inverseStep m x y) (1 % m)

end DetDLP_M13A_IrredHermite


