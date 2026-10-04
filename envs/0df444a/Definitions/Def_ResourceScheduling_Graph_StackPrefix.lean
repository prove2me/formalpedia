-- Prove2me | Definitions.Def_ResourceScheduling_Graph_StackPrefix
-- name    : ResourceScheduling_Graph_StackPrefix
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T12:36:40.170192+00:00
-- url     : https://prove2.me/theorems/05fab6e2-75e0-4f5d-aacf-84745f15d6ec
-- title:
--   ResourceScheduling Graph StackPrefix
-- statement:
--   Consume leading unary ones into a counter stack, stopping before the first separator or at the end.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram
import Definitions.Def_ResourceScheduling_Graph_WordProgram

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

def prefixAct {K : Type} [DecidableEq K] (input count : K)
    (_h : K → Option Letter) (k : K) : StackAct Letter :=
  if k = input then .pop else if k = count then .push .one else .keep

/-- Count leading unary ones, leaving the separator (if any) under the input stack top. -/
def prefixProg {K : Type} [DecidableEq K] (input count : K) : StackProg K Letter :=
  .loop (fun h => decide (h input = some .one)) (.act (prefixAct input count))

end ResourceScheduling.Graph


