-- Prove2me | Definitions.Def_BKAR_CubePartition_Branches
-- name    : BKAR_CubePartition_Branches
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:45:27.933772+00:00
-- url     : https://prove2.me/theorems/5e83e51a-4954-485a-91a2-32361ff53a01
-- title:
--   Branches
-- statement:
--   Definitions and structural lemmas for Branches, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean

import Definitions.Def_BKAR_CubePartition_Orders
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace OrderedGrowth
variable {F G : Forest V} {order : List (Edge V)}
end OrderedGrowth
namespace TerminalGrowth
variable {F : Forest V}
end TerminalGrowth
end Forest
end BKAR


