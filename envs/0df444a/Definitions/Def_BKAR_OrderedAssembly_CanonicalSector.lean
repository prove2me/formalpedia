-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
-- name    : BKAR_OrderedAssembly_CanonicalSector
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:59:37.32788+00:00
-- url     : https://prove2.me/theorems/be15e949-c1a3-4d5a-b646-af4141887c8a
-- title:
--   Canonical Sector
-- statement:
--   Definitions and structural lemmas for Canonical Sector, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CanonicalSector.lean

import Definitions.Def_BKAR_OrderedAssembly_ChosenGrowth
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace OrderedGrowth
variable {G : Forest V} {order : List (Edge V)}
end OrderedGrowth
end Forest
end BKAR


