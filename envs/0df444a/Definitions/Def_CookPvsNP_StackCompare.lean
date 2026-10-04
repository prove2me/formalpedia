-- Prove2me | Definitions.Def_CookPvsNP_StackCompare
-- name    : CookPvsNP_StackCompare
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:35:51.466568+00:00
-- url     : https://prove2.me/theorems/188f2d86-0904-43dc-b2b0-568961d65eac
-- title:
--   CookPvsNP StackCompare
-- statement:
--   A loop that pops two stacks while both are nonempty.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros

set_option autoImplicit false
namespace CookPvsNP

def syncPopAct {K A : Type} [DecidableEq K] (i j : K)
    (_h : K → Option A) (k : K) : StackAct A :=
  if k = i ∨ k = j then .pop else .keep

def syncPopProg {K A : Type} [DecidableEq K] (i j : K) : StackProg K A :=
  .loop (fun h => (h i).isSome && (h j).isSome) (.act (syncPopAct i j))

end CookPvsNP


