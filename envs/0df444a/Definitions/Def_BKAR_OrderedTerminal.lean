-- Prove2me | Definitions.Def_BKAR_OrderedTerminal
-- name    : BKAR_OrderedTerminal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:31:46.456543+00:00
-- url     : https://prove2.me/theorems/fbc6e678-7117-5fa5-b2d8-dba6d2282d5a
-- title:
--   Ordered Terminal
-- statement:
--   Definitions and structural lemmas for Ordered Terminal, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminal.lean

import Definitions.Def_BKAR_OrderedBranch
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveExtension
variable {F : Forest V} {e : Edge V}
def singletonGrowth (h : ActiveExtension F e) :
    OrderedGrowth F [e] h.forest :=
  OrderedGrowth.cons h.extension (OrderedGrowth.nil h.forest)
end ActiveExtension
end Forest
end BKAR


