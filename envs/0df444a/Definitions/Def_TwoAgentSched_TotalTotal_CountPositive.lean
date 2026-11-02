-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_CountPositive
-- name    : TwoAgentSched_TotalTotal_CountPositive
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T21:39:45.810806+00:00
-- url     : https://prove2.me/theorems/8f8e4e5b-9071-4a24-b008-7579692c692e
-- title:
--   Finite stack program counting nonzero canonical binary blocks
-- statement:
--   A finite four-stack program scans consecutive separator-terminated natural-number blocks. It parses a block, increments a unary count when the canonical digit block is nonempty, and clears the digit scratch stack before continuing. The loop runs while input remains and the most recent parser status is successful.
--
--   This is the first-pass counting component for the directly ordered even PARTITION gadget. It is an auxiliary machine construction, not a construction stated in the cited paper. Correctness on canonical input and termination on arbitrary input are stated separately.
-- source:
--   Supporting implementation for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. Counting nonzero binary blocks is an auxiliary formalization component.

import Mathlib
import Definitions.Def_CookPvsNP_StackMacros
import Definitions.Def_StackProgPortLift
import Definitions.Def_CookPvsNP_CanonicalBlockParser

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.CountPositive

open StackProgPortLift CookPvsNP.CanonicalBlockParser

/-- Input, reversed digits, parser status, and a unary positive-count stack. -/
def store4 (input digits status count : List BSym) : Fin 4 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then digits else if k = 2 then status else count

def parsePorts : Fin 3 ↪ Fin 4 := ⟨![0,1,2], by decide⟩
def parseInverse : Fin 4 → Option (Fin 3) := ![some 0,some 1,some 2,none]

def incrementTest (h : Fin 4 → Option BSym) : Bool :=
  (h 2 == some BSym.one) && (h 1).isSome
def incrementAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 3 then .push .one else .keep
def keepAct (_h : Fin 4 → Option BSym) (_k : Fin 4) : StackAct BSym := .keep

def continueTest (h : Fin 4 → Option BSym) : Bool :=
  (h 0).isSome && (h 2 == some BSym.one)

/-- Parse one block, increment on a nonzero canonical block, and clear digits. -/
def countBody : StackProg (Fin 4) BSym :=
  .seq (liftProgC parsePorts parseInverse parseCanonicalBlockProg)
    (.seq (.branch incrementTest (.act incrementAct) (.act keepAct)) (clearProg 1))

/-- Scan blocks while the input is nonempty and the last parser status is valid. -/
def countPositive : StackProg (Fin 4) BSym := .loop continueTest countBody


end TwoAgentSched.TotalTotal.CountPositive


