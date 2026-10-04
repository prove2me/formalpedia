-- Prove2me | Definitions.Def_CookPvsNP_StackLookup
-- name    : CookPvsNP_StackLookup
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:35:35.421737+00:00
-- url     : https://prove2.me/theorems/bcdfd41e-6309-4a40-a291-3fbb49f8ac3a
-- title:
--   CookPvsNP StackLookup
-- statement:
--   A six-port indexed word lookup program using preserved source and index stacks and four cleared scratch stacks.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
namespace CookPvsNP

def peekPushAct {K A : Type} [DecidableEq K] (src dst : K) (fallback : A)
    (h : K → Option A) (k : K) : StackAct A :=
  if k = dst then .push ((h src).getD fallback) else .keep

/-- Ports are word, unary index, result, word scratch, index scratch, copy scratch. -/
def lookupProg {K A : Type} [DecidableEq K] (r : Fin 6 ↪ K) (fallback : A) : StackProg K A :=
  .seq (copyProg (r 0) (r 3) (r 5))
    (.seq (copyProg (r 1) (r 4) (r 5))
      (.seq (consumeProg (r 4) (fun k => decide (k = r 3)))
        (.seq (.act (peekPushAct (r 3) (r 2) fallback)) (clearProg (r 3)))))

end CookPvsNP


