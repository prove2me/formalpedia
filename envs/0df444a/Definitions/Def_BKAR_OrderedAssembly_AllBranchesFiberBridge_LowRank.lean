-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
-- name    : BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:07:11.313865+00:00
-- url     : https://prove2.me/theorems/c4d1b73e-260c-4b4a-aeb8-1756c7426729
-- title:
--   Low Rank
-- statement:
--   Definitions and structural lemmas for Low Rank, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
end Forest
end BKAR


