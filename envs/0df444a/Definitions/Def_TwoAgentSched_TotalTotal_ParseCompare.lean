-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_ParseCompare
-- name    : TwoAgentSched_TotalTotal_ParseCompare
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:40:34.61052+00:00
-- url     : https://prove2.me/theorems/2908e665-016c-4501-a2ba-edeeffe4cfc4
-- title:
--   Finite stack program to parse and compare two binary naturals
-- statement:
--   A finite five-stack program that applies a canonical binary-block parser twice and then compares the resulting most-significant-bit-first digit stacks. Its stacks hold the unread input, the two digit strings, parser status, and comparison state. The component uses explicit finite-port embeddings to share the global store.
--
--   Correctness for two canonical input blocks and a linear termination bound on arbitrary inputs are stated separately. The program is a parsing and comparison component of the scheduling reduction; the complete sorting and encoding transducer are separate work.
-- source:
--   Supporting implementation for Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2, pp. 237–238. This stack-program composition is an additional formalization component and is not stated in the paper.

import Mathlib
import Definitions.Def_StackProgPortLift
import Definitions.Def_CookPvsNP_CanonicalBlockParser
import Definitions.Def_TwoAgentSched_TotalTotal_StackCompareDigits

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.ParseCompare

open StackProgPortLift CookPvsNP.CanonicalBlockParser TwoAgentSched.TotalTotal.StackCompareDigits

/-- Input remainder, two digit stacks, parser status, and comparison states. -/
def store5 (input left right status result : List BSym) : Fin 5 → List BSym :=
  fun k => if k = 0 then input else if k = 1 then left else if k = 2 then right
    else if k = 3 then status else result

def leftPorts : Fin 3 ↪ Fin 5 := ⟨![0,1,3], by decide⟩
def leftInverse : Fin 5 → Option (Fin 3) := ![some 0,some 1,none,some 2,none]
def rightPorts : Fin 3 ↪ Fin 5 := ⟨![0,2,3], by decide⟩
def rightInverse : Fin 5 → Option (Fin 3) := ![some 0,none,some 1,some 2,none]
def comparePorts : Fin 3 ↪ Fin 5 := ⟨![1,2,4], by decide⟩
def compareInverse : Fin 5 → Option (Fin 3) := ![none,some 0,some 1,none,some 2]

/-- Parse two canonical binary natural blocks and compare their reversed digit
    stacks. This component leaves the remaining input untouched. -/
def parseCompare : StackProg (Fin 5) BSym :=
  .seq (liftProgC leftPorts leftInverse parseCanonicalBlockProg)
    (.seq (liftProgC rightPorts rightInverse parseCanonicalBlockProg)
      (liftProgC comparePorts compareInverse compareFullProg))


end TwoAgentSched.TotalTotal.ParseCompare


