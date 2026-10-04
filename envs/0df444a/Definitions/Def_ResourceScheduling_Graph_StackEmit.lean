-- Prove2me | Definitions.Def_ResourceScheduling_Graph_StackEmit
-- name    : ResourceScheduling_Graph_StackEmit
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T13:58:04.877996+00:00
-- url     : https://prove2.me/theorems/7ced9e90-8770-4add-be97-6522eb9db4d1
-- title:
--   ResourceScheduling Graph StackEmit
-- statement:
--   Emit a separator-terminated unary field onto a reversed output stack, preserving the source number stack.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMapTransfer
import Definitions.Def_ResourceScheduling_Graph_WordProgram

set_option autoImplicit false
namespace ResourceScheduling.Graph
open CookPvsNP

/-- Emit one unary field onto the reversed output. Ports: number, output, work, scratch. -/
def emitUnaryProg {K : Type} [DecidableEq K] (r : Fin 4 ↪ K) : StackProg K Letter :=
  .seq (copyProg (r 0) (r 2) (r 3))
    (.seq (mapTransferProg (r 2) (fun k => decide (k = r 1)) (fun _ => Letter.one))
      (pushProg (r 1) Letter.sep))

end ResourceScheduling.Graph


