-- Prove2me | Definitions.Def_BKAR_CubePartition_Support_Terminal
-- name    : BKAR_CubePartition_Support_Terminal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:53:41.851792+00:00
-- url     : https://prove2.me/theorems/492d1d4b-4f73-5f8a-81ac-7cca261ae9f4
-- title:
--   Terminal
-- statement:
--   Definitions and structural lemmas for Terminal, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Support/Terminal.lean

import Definitions.Def_BKAR_CubePartition_Support_Contribution
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace ActiveTerminalBranchData
variable {F : Forest V}
end ActiveTerminalBranchData
end Forest
end BKAR


