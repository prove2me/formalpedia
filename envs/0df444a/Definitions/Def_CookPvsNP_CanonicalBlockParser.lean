-- Prove2me | Definitions.Def_CookPvsNP_CanonicalBlockParser
-- name    : CookPvsNP_CanonicalBlockParser
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:35:27.784682+00:00
-- url     : https://prove2.me/theorems/6d2823b7-2159-4cb4-bf1c-25a3bcb59d39
-- title:
--   Finite stack parser for a canonical separator-terminated binary natural
-- statement:
--   A finite three-stack program for reading the first separator-terminated natural-number block over the four-symbol alphabet. It scans binary digits into a reversed stack, consumes a separator when present, and records status markers for delimiter validity and canonicality. The empty digit block is the encoding of zero; a nonempty canonical digit block must end in one.
--
--   The stack program is shared infrastructure for binary reductions. Its behaviour and linear source-step bounds, including on malformed input, are stated separately.
-- source:
--   Supporting stack-machine implementation for binary encodings in Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This canonical parser is an auxiliary implementation, not a claim from the paper.

import Mathlib
import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace CookPvsNP.CanonicalBlockParser

/-- Three stacks hold unconsumed input, reversed digits, and status markers. -/
def store (input acc status : List BSym) : Fin 3 → List BSym :=
  fun k ↦ if k = 0 then input else if k = 1 then acc else status

def digitSym (b : Bool) : BSym := if b then .one else .zero

def isDigit (o : Option BSym) : Bool :=
  match o with
  | some .zero | some .one => true
  | _ => false

def digitTest (h : Fin 3 → Option BSym) : Bool := isDigit (h 0)
def separatorTest (h : Fin 3 → Option BSym) : Bool := h 0 == some BSym.sep

def readAct (h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 1 then
    match h 0 with
    | some .zero => .push .zero
    | some .one => .push .one
    | _ => .keep
  else .keep

def acceptAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 0 then .pop else if k = 2 then .push .one else .keep

def rejectAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- A finite program that reads the first 0/1 block, consumes its separator
    on success, and pushes one status marker: one for a separator, zero for a
    missing separator or illegal next symbol. -/
def parseBlockProg : StackProg (Fin 3) BSym :=
  .seq (.loop digitTest (.act readAct))
    (.branch separatorTest (.act acceptAct) (.act rejectAct))

/-- A terminated block is canonical when it is empty or has most significant
    digit one; status zero from the first stage is always rejected. -/
def canonicalTest (h : Fin 3 → Option BSym) : Bool :=
  (h 2 == some BSym.one) &&
    match h 1 with
    | none | some .one => true
    | _ => false

def markTrueAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .one else .keep

def markFalseAct (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push .zero else .keep

/-- The delimiter parser followed by a finite-control canonicality check.
    The top status marker is one exactly on a terminated block that is empty
    or ends in one; the previous delimiter status is kept just below it. -/
def parseCanonicalBlockProg : StackProg (Fin 3) BSym :=
  .seq parseBlockProg (.branch canonicalTest (.act markTrueAct) (.act markFalseAct))


end CookPvsNP.CanonicalBlockParser


