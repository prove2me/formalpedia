-- Prove2me | Definitions.Def_BKAR_CubePartition_Prefixed
-- name    : BKAR_CubePartition_Prefixed
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:48:51.853731+00:00
-- url     : https://prove2.me/theorems/0c652d13-b110-4252-9865-bc0fe6dbf61e
-- title:
--   Prefixed
-- statement:
--   Definitions and structural lemmas for Prefixed, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Prefixed.lean

import Definitions.Def_BKAR_CubePartition_Branches
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


