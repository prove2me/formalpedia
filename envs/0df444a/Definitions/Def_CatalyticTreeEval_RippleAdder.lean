-- Prove2me | Definitions.Def_CatalyticTreeEval_RippleAdder
-- name    : CatalyticTreeEval_RippleAdder
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T02:23:03.995587+00:00
-- url     : https://prove2.me/theorems/af3c07d9-45dd-4484-9119-669fbe974f29
-- title:
--   Native binary ripple adder on tagged work columns
-- statement:
--   A fourteen-state binary machine processes columns true,a,b and a false terminating tag. It keeps the carry in finite control, preserves the b slots, and writes sum bits into the a slots. Its final step writes carry to the terminator. The column and bank execution theorems, time, workspace and frames are separate obligations.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Section 3.4, Lemma 3.19, binary modular arithmetic infrastructure.

import Definitions.Def_CatalyticTreeEval_MachineContracts

set_option autoImplicit false

namespace CatalyticTreeEval.Contracts.RippleAdder

open CatalyticMatching.General

def marker (carry : Bool) : Fin 14 := ⟨if carry then 1 else 0, by cases carry <;> decide⟩
def readA (carry : Bool) : Fin 14 := ⟨if carry then 3 else 2, by cases carry <;> decide⟩
def readB (carry a : Bool) : Fin 14 :=
  ⟨4 + 2 * carry.toNat + a.toNat, by cases carry <;> cases a <;> decide⟩
def writeA (carry sum : Bool) : Fin 14 :=
  ⟨8 + 2 * carry.toNat + sum.toNat, by cases carry <;> cases sum <;> decide⟩
def skipB (carry : Bool) : Fin 14 := ⟨if carry then 13 else 12, by cases carry <;> decide⟩

def sumBit (carry a b : Bool) : Bool := (carry ^^ a) ^^ b
def carryBit (carry a b : Bool) : Bool := (carry && a) || (carry && b) || (a && b)

def markerInstruction (carry bit : Bool) : Instruction 14 where
  next := if bit then some (readA carry) else none
  workWrite := if bit then bit else carry
  catalystWrite := none
  inputMove := .stay
  workMove := if bit then .right else .stay
  catalystMove := .stay
  emit := none

def readAInstruction (carry bit : Bool) : Instruction 14 where
  next := some (readB carry bit)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def readBInstruction (carry a bit : Bool) : Instruction 14 where
  next := some (writeA (carryBit carry a bit) (sumBit carry a bit))
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .left
  catalystMove := .stay
  emit := none

def writeAInstruction (carry sum : Bool) : Instruction 14 where
  next := some (skipB carry)
  workWrite := sum
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

def skipBInstruction (carry bit : Bool) : Instruction 14 where
  next := some (marker carry)
  workWrite := bit
  catalystWrite := none
  inputMove := .stay
  workMove := .right
  catalystMove := .stay
  emit := none

/-- A native 14-state ripple adder on work columns `true,a,b`, followed by one
false sentinel. Each column takes five transitions, preserves `b`, and replaces
`a` by its sum bit. The final transition writes the carry into the sentinel and
halts there. Input, catalyst, and output do not change. -/
def machine : Main.Machine where
  states := 14
  start := marker false
  table q _ bit _ _ _ _ :=
    match q.val with
    | 0 => markerInstruction false bit
    | 1 => markerInstruction true bit
    | 2 => readAInstruction false bit
    | 3 => readAInstruction true bit
    | 4 => readBInstruction false false bit
    | 5 => readBInstruction false true bit
    | 6 => readBInstruction true false bit
    | 7 => readBInstruction true true bit
    | 8 => writeAInstruction false false
    | 9 => writeAInstruction false true
    | 10 => writeAInstruction true false
    | 11 => writeAInstruction true true
    | 12 => skipBInstruction false bit
    | _ => skipBInstruction true bit

def cursor (c : Config machine) (head : ℕ) (q : Option (Fin 14)) : Config machine :=
  { c with state := q, workHead := head }

def writeSum (c : Config machine) (head : ℕ) (sum : Bool) : Config machine :=
  { c with work := Function.update c.work (head + 1) sum }

end CatalyticTreeEval.Contracts.RippleAdder


