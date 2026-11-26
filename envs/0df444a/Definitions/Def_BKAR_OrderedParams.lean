-- Prove2me | Definitions.Def_BKAR_OrderedParams
-- name    : BKAR_OrderedParams
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:29:13.062809+00:00
-- url     : https://prove2.me/theorems/d35e0b9f-b20a-4451-b73a-d006e27244cd
-- title:
--   Ordered Params
-- statement:
--   Definitions and structural lemmas for Ordered Params, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean

import Definitions.Def_BKAR_OrderedSimplex
import Theorems.Thm_BKAR_OrderedSimplexParams_tail

set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace EdgeExtension
variable {F F' : Forest V} {e : Edge V}
end EdgeExtension
namespace OrderedGrowth
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
def params {F G : Forest V} {order : List (Edge V)}
    (h : OrderedGrowth F order G) :
    (F.EdgeParam → ℝ) → List ℝ → G.EdgeParam → ℝ :=
  match h with
  | nil _ => fun u _ => u
  | cons step tail => fun u ts =>
      match ts with
      | [] => tail.params (step.extendParam u 0) []
      | t :: ts => tail.params (step.extendParam u t) ts
end OrderedGrowth
end Forest
end BKAR


