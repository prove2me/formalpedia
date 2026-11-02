-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdder
-- name    : TwoAgentSched_TotalTotal_BinaryAdder
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T21:04:04.894767+00:00
-- url     : https://prove2.me/theorems/b8d9c4fa-d127-4711-a35b-a61861cf7c01
-- title:
--   Finite stack binary adder for unequal input lengths
-- statement:
--   A finite four-stack full-adder loop reads two little-endian binary digit stacks and a carry, emitting sum digits on an output stack. It treats a missing input digit as zero and runs while either input stack remains nonempty. The final carry stays on the carry stack. A pure reference recursion describes the low output digits and final carry.
--
--   This program is supporting threshold arithmetic for the two-agent scheduling encoding reduction. Its execution bound and arithmetic correctness are stated separately; it is not a claim from the source paper.
-- source:
--   Supporting machine construction for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. The binary stack adder is an auxiliary formalization construction.

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.BinaryAdder

/-- Left and right input bits, reversed output bits, and a stack of carries. -/
def store (left right output carries : List BSym) : Fin 4 → List BSym :=
  fun k => if k = 0 then left else if k = 1 then right else if k = 2 then output else carries

def bitSym (b : Bool) : BSym := if b then .one else .zero
def bitValue (b : Bool) : ℕ := if b then 1 else 0

def sumBit (x y c : Bool) : Bool := xor (xor x y) c
def carryBit (x y c : Bool) : Bool := (x && y) || (x && c) || (y && c)

def asBit (o : Option BSym) : Bool := o == some BSym.one
def addAct (h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 0 ∨ k = 1 then .pop
  else if k = 2 then .push (bitSym (sumBit (asBit (h 0)) (asBit (h 1)) (asBit (h 3))))
  else .push (bitSym (carryBit (asBit (h 0)) (asBit (h 1)) (asBit (h 3))))

/-- One finite-stack full-adder transition; absent input bits act as zeros. -/
def adderStep : StackProg (Fin 4) BSym := .act addAct


/-- Addition of unequal-length little-endian inputs, returning low bits and
    the final carry after all input positions have been consumed. -/
def addFullAux : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], c => ([], c)
  | x :: xs, [], c =>
      let r := addFullAux xs [] (carryBit x false c)
      (sumBit x false c :: r.1, r.2)
  | [], y :: ys, c =>
      let r := addFullAux [] ys (carryBit false y c)
      (sumBit false y c :: r.1, r.2)
  | x :: xs, y :: ys, c =>
      let r := addFullAux xs ys (carryBit x y c)
      (sumBit x y c :: r.1, r.2)
termination_by left right _ => left.length + right.length

def bitWordValue (bits : List Bool) : ℕ := Nat.ofDigits 2 (bits.map bitValue)

def eitherNonempty (h : Fin 4 → Option BSym) : Bool :=
  (h 0).isSome || (h 1).isSome

/-- Run one full-adder step per occupied input position, treating an absent
    bit as zero. The final carry remains on the carry stack. -/
def adderFullLoop : StackProg (Fin 4) BSym := .loop eitherNonempty adderStep

end TwoAgentSched.TotalTotal.BinaryAdder


