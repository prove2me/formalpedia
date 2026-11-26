-- Prove2me | Definitions.Def_BKAR_OrderedRecursion
-- name    : BKAR_OrderedRecursion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:33:29.507816+00:00
-- url     : https://prove2.me/theorems/724dbe9e-c02f-4b23-b42c-14288e4161c1
-- title:
--   Ordered Recursion
-- statement:
--   Definitions and structural lemmas for Ordered Recursion, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRecursion.lean

import Definitions.Def_BKAR_OrderedTerminal
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
def consGrowth (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G) :
    OrderedGrowth F (e :: order) G :=
  OrderedGrowth.cons h.extension tail
end ActiveExtension
end Forest
end BKAR


