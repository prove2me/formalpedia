-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMFields
-- name    : ResourceScheduling_Graph_RAMFields
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T15:22:52.225894+00:00
-- url     : https://prove2.me/theorems/64f33986-83f9-46e1-95c9-f2289fab012b
-- title:
--   ResourceScheduling Graph RAMFields
-- statement:
--   The input/output effects of register programs and a common word-field projection.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMCode

set_option autoImplicit false
namespace ResourceScheduling.Graph

def RAMState.field {V : Type} (s : RAMState V) (b : Bool) : List Letter :=
  if b then s.word else s.out

def RAMCode.effect {V : Type} : RAMCode V → Bool → Bool
  | .emit _, b => !b
  | .parse _ _ _, b => b
  | .seq p q, b | .branch _ p q, b => p.effect b || q.effect b
  | .loop _ p, b => p.effect b
  | _, _ => false

end ResourceScheduling.Graph


