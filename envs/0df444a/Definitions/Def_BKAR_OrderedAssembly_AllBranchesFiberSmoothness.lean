-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
-- name    : BKAR_OrderedAssembly_AllBranchesFiberSmoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:04:13.286052+00:00
-- url     : https://prove2.me/theorems/56f8d8d9-fd6c-412f-9275-f34248014a88
-- title:
--   All Branches Fiber Smoothness
-- statement:
--   Definitions and structural lemmas for All Branches Fiber Smoothness, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberSmoothness.lean

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
end BKARContDiff
end BKAR


