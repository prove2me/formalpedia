-- Prove2me | Definitions.Def_BKAR_OrderedAssembly
-- name    : BKAR_OrderedAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:09:46.591809+00:00
-- url     : https://prove2.me/theorems/dfc51cbd-c631-4d8f-a45c-6cea571a79e5
-- title:
--   Ordered Assembly
-- statement:
--   Definitions and structural lemmas for Ordered Assembly, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly.lean

import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge
import Definitions.Def_BKAR_OrderedAssembly_CanonicalForestBridge
import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
import Definitions.Def_BKAR_OrderedAssembly_CubeFold
import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false


