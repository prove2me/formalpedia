-- Prove2me | Definitions.Def_CookPvsNP_StackRepeat
-- name    : CookPvsNP_StackRepeat
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:35:30.072991+00:00
-- url     : https://prove2.me/theorems/d5f9fcb4-e15e-45f0-a256-c8533d9a39c2
-- title:
--   CookPvsNP StackRepeat
-- statement:
--   Repeatedly copy a fixed word into a destination while consuming a unary counter.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
namespace CookPvsNP

/-- Ports are immutable source word, destination, consumed loop counter, empty scratch. -/
def repeatCopyProg {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K) : StackProg K A :=
  .loop (fun h => (h (r 2)).isSome)
    (.seq (popProg (r 2)) (copyProg (r 0) (r 1) (r 3)))

end CookPvsNP


