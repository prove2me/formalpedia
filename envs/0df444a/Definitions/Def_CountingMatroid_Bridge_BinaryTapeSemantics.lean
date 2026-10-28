-- Prove2me | Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
-- name    : CountingMatroid_Bridge_BinaryTapeSemantics
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T19:13:48.849202+00:00
-- url     : https://prove2.me/theorems/50a22185-5645-4b25-aaea-58b5be3fbd48
-- title:
--   Head-relative semantics for a two-stack binary tape
-- statement:
--   A binary tape is represented by two stacks relative to its head. The left stack stores cells to the left in reverse order; the right stack stores the current cell followed by cells to the right. Missing cells have value false. The representation assigns every relative tape position a Boolean value.
-- source:
--   Lean 4.33.1 semantic representation for the verified register-machine tape operations.

import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveLeft
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveRight

set_option autoImplicit false

namespace CountingMatroid.Bridge

/-- A tape viewed relative to its current head, represented by two stacks.
`left i` is the cell at distance `i+1` to the left; `right i` is the cell at
distance `i` to the right, with distance zero being the current cell. -/
inductive BinaryTapePosition where
  | left (distance : ℕ)
  | right (distance : ℕ)
  deriving DecidableEq

def binaryStackRead (xs : List Bool) (i : ℕ) : Bool :=
  (xs[i]?).getD false

def binaryTapeAt (left right : List Bool) : BinaryTapePosition → Bool
  | .left i => binaryStackRead left i
  | .right i => binaryStackRead right i

end CountingMatroid.Bridge


