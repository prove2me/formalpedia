-- Prove2me | Definitions.Def_ResourceScheduling_Graph_RAMSafe
-- name    : ResourceScheduling_Graph_RAMSafe
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T15:41:09.415987+00:00
-- url     : https://prove2.me/theorems/db286a7a-c551-4792-80a5-1014082d133b
-- title:
--   ResourceScheduling Graph RAMSafe
-- statement:
--   A structured-program numeric bound paired with the same bound on the final state.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_ResourceScheduling_Graph_RAMBudget

set_option autoImplicit false
namespace ResourceScheduling.Graph

def RAMSafe {V : Type} [DecidableEq V] (p : RAMCode V) (B : ℕ) (s : RAMState V) : Prop :=
  p.Bounded B s ∧ RAMBound B (p.eval s)

end ResourceScheduling.Graph


