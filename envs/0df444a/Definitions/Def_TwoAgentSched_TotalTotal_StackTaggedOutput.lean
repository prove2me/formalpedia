-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_StackTaggedOutput
-- name    : TwoAgentSched_TotalTotal_StackTaggedOutput
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T20:12:43.540652+00:00
-- url     : https://prove2.me/theorems/912bfc44-c6bb-4184-9182-ef9458c71bea
-- title:
--   Finite stack program for emitting a binary PARTITION gadget tag
-- statement:
--   A finite three-stack program for one tagged output word in the distinct-even PARTITION gadget. The first two stacks are unary counters; the third holds an existing binary word. The program consumes the counters and pushes a prescribed pattern of zero symbols and one marker in front of the word. All tests and actions inspect only stack tops.
--
--   The stack program is an additional implementation component for the scheduling reduction and is not asserted in the source paper. Its execution cost and its agreement with the binary gadget are separate theorems.
-- source:
--   Agnetis, Mirchandani, Pacciarelli and Pacifici, Scheduling Problems with Two Competing Agents, Operations Research 52(2), 2004, Theorem 9.2 and proof, pp. 237–238. This finite stack program implements a new supporting PARTITION tagging gadget and is not described in the paper.

import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ProjSchedTW_Complexity_Encoding

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.StackTaggedOutput

/-- Two counter stacks and a stack containing the encoded source weight. -/
def store (i d output : List BSym) : Fin 3 → List BSym :=
  fun k => if k = 0 then i else if k = 1 then d else output

def nonempty (j : Fin 3) (h : Fin 3 → Option BSym) : Bool := (h j).isSome
def pushAct (a : BSym) (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = 2 then .push a else .keep
def consumeAct (j : Fin 3) (_h : Fin 3 → Option BSym) (k : Fin 3) : StackAct BSym :=
  if k = j then .pop else if k = 2 then .push BSym.zero else .keep

/-- Consume one counter cell and emit two zeros per iteration. -/
def doubleZero (j : Fin 3) : StackProg (Fin 3) BSym :=
  .loop (nonempty j) (.seq (.act (pushAct .zero)) (.act (consumeAct j)))

/-- Starting with an encoded positive weight on the output stack, consume the
    two unary counters and prepend the zero runs and marker used by the
    distinct-even PARTITION gadget. -/
def taggedOutput : StackProg (Fin 3) BSym :=
  .seq (doubleZero 1)
    (.seq (.act (pushAct .zero))
      (.seq (.act (pushAct .one))
        (.seq (doubleZero 0) (.act (pushAct .zero)))))

end TwoAgentSched.TotalTotal.StackTaggedOutput


