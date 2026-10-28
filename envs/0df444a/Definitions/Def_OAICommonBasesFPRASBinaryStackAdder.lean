-- Prove2me | Definitions.Def_OAICommonBasesFPRASBinaryStackAdder
-- name    : OAICommonBasesFPRASBinaryStackAdder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T03:26:49.540993+00:00
-- url     : https://prove2.me/theorems/dc0e874f-e897-4928-aadf-1e7582c33080
-- title:
--   Fixed binary stack adder program
-- statement:
--   A fixed binary-register stack program that adds two little-endian bit lists, handles carry and unequal lengths, and returns the sum through the machine's fixed halt output registers.
-- source:
--   Lean 4.33.1 reusable machine-arithmetic contribution to the existing Approximate counting of common bases of two matroids mission. This fixed stack program is an arithmetic component, not the estimator implementation.

import Definitions.Def_CommonBasesFPRAS
set_option autoImplicit false

namespace OAI.CommonBasesFPRAS

def adderState (q : ℕ) : Fin 22 := ⟨q % 22, Nat.mod_lt _ (by omega)⟩
def adderReg (r : ℕ) : Fin 10 := ⟨r % 10, Nat.mod_lt _ (by omega)⟩

/-- A fixed stack program for adding two little-endian binary natural numbers.
Input stacks are in registers 6 and 7, output sum in 6, denominator one in 7,
and temporary bits in register 8. -/
def binaryStackAdder : Program 2 21 := fun q =>
  match q.val with
  | 0 => .pop (adderReg 6) (adderState 1) (adderState 2) (adderState 3)
  | 1 => .pop (adderReg 7) (adderState 16) (adderState 8) (adderState 9)
  | 2 => .pop (adderReg 7) (adderState 8) (adderState 8) (adderState 9)
  | 3 => .pop (adderReg 7) (adderState 10) (adderState 10) (adderState 11)
  | 4 => .pop (adderReg 6) (adderState 5) (adderState 6) (adderState 7)
  | 5 => .pop (adderReg 7) (adderState 17) (adderState 12) (adderState 13)
  | 6 => .pop (adderReg 7) (adderState 12) (adderState 12) (adderState 13)
  | 7 => .pop (adderReg 7) (adderState 14) (adderState 14) (adderState 15)
  | 8 => .push (adderReg 8) false (adderState 0)
  | 9 => .push (adderReg 8) true (adderState 0)
  | 10 => .push (adderReg 8) true (adderState 0)
  | 11 => .push (adderReg 8) false (adderState 4)
  | 12 => .push (adderReg 8) true (adderState 0)
  | 13 => .push (adderReg 8) false (adderState 4)
  | 14 => .push (adderReg 8) false (adderState 4)
  | 15 => .push (adderReg 8) true (adderState 4)
  | 16 => .pop (adderReg 8) (adderState 18) (adderState 19) (adderState 20)
  | 17 => .push (adderReg 8) true (adderState 16)
  | 18 => .push (adderReg 7) true (adderState 21)
  | 19 => .push (adderReg 6) false (adderState 16)
  | 20 => .push (adderReg 6) true (adderState 16)
  | 21 => .halt
  | _ => .halt

def addColumn (a b carry : Bool) : Bool × Bool :=
  match a, b, carry with
  | false, false, false => (false, false)
  | false, false, true => (true, false)
  | false, true, false => (true, false)
  | false, true, true => (false, true)
  | true, false, false => (true, false)
  | true, false, true => (false, true)
  | true, true, false => (false, true)
  | true, true, true => (true, true)

def addBitsPass : Bool → List Bool → List Bool → List Bool × Bool
  | carry, [], [] => ([], carry)
  | carry, a :: as, [] =>
      let col := addColumn a false carry
      let tail := addBitsPass col.2 as []
      (col.1 :: tail.1, tail.2)
  | carry, [], b :: bs =>
      let col := addColumn false b carry
      let tail := addBitsPass col.2 [] bs
      (col.1 :: tail.1, tail.2)
  | carry, a :: as, b :: bs =>
      let col := addColumn a b carry
      let tail := addBitsPass col.2 as bs
      (col.1 :: tail.1, tail.2)
termination_by carry a b => a.length + b.length

def addBitsAux (carry : Bool) : List Bool → List Bool → List Bool
  | [], [] => if carry then [true] else []
  | a :: as, [] =>
      let col := addColumn a false carry
      col.1 :: addBitsAux col.2 as []
  | [], b :: bs =>
      let col := addColumn false b carry
      col.1 :: addBitsAux col.2 [] bs
  | a :: as, b :: bs =>
      let col := addColumn a b carry
      col.1 :: addBitsAux col.2 as bs
termination_by a b => a.length + b.length

def adderFinalScratch (a b : List Bool) : List Bool :=
  let pass := addBitsPass false a b
  if pass.2 then true :: pass.1.reverse else pass.1.reverse

def adderCarrySteps (a b : List Bool) : ℕ :=
  if (addBitsPass false a b).2 then 3 else 2

def adderTotalSteps (a b : List Bool) : ℕ :=
  3 * max a.length b.length + adderCarrySteps a b +
    2 * (adderFinalScratch a b).length + 3

end OAI.CommonBasesFPRAS


