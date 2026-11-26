-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_CubeFold
-- name    : BKAR_OrderedAssembly_CubeFold
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:01:03.971327+00:00
-- url     : https://prove2.me/theorems/54996aff-c8a2-4feb-a0b8-bc557b30f500
-- title:
--   Cube Fold
-- statement:
--   Definitions and structural lemmas for Cube Fold, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/CubeFold.lean

import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Definitions.Def_BKAR_OrderedAssembly_CanonicalSector
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
end Forest
end BKAR


