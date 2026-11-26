-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
-- name    : BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:04:50.56928+00:00
-- url     : https://prove2.me/theorems/0f11608b-7e90-505d-ac1e-02abf0d894b9
-- title:
--   Core
-- statement:
--   Definitions and structural lemmas for Core, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
end Forest
end BKAR


