-- Prove2me | Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdderNormalizer
-- name    : TwoAgentSched_TotalTotal_BinaryAdderNormalizer
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T22:36:55.026681+00:00
-- url     : https://prove2.me/theorems/0176d349-187c-4f3f-9c8f-06d21dd17097
-- title:
--   Four-stack binary-adder output normalizer
-- statement:
--   A fixed four-stack normalizer removes leading zeros from a most-significant-bit-first output, transfers the remaining bits in reverse to the input stack, clears the carry history, and resets the carry stack to zero. It is a component for repeated binary addition.

import Definitions.Def_TwoAgentSched_TotalTotal_BinaryAdder
import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
open CookPvsNP ProjSchedTW.Complexity

namespace TwoAgentSched.TotalTotal.BinaryAdder.Normalizer

/-- Continue while the MSB-first output begins with a redundant zero. -/
def zeroOnOutput (h : Fin 4 → Option BSym) : Bool := h 2 == some BSym.zero

def dropOutputAct (_h : Fin 4 → Option BSym) (k : Fin 4) : StackAct BSym :=
  if k = 2 then .pop else .keep

/-- Discard leading zero symbols from the output stack. -/
def trimOutput : StackProg (Fin 4) BSym := .loop zeroOnOutput (.act dropOutputAct)

/-- Trim the high-zero prefix, reverse the remaining output onto input stack
    zero, clear the carry history, and reset carry to zero. -/
def normalizeOutput : StackProg (Fin 4) BSym :=
  .seq trimOutput
    (.seq (transferProg 2 (fun k => decide (k = 0)))
      (.seq (clearProg 3) (pushProg 3 .zero)))

end TwoAgentSched.TotalTotal.BinaryAdder.Normalizer


