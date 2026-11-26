-- Prove2me | Definitions.Def_BKAR_CubePartition_MeasureSmoothness
-- name    : BKAR_CubePartition_MeasureSmoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:50:08.483868+00:00
-- url     : https://prove2.me/theorems/4cd8e7ef-a690-4014-a5bb-65d84efc6fe1
-- title:
--   Measure Smoothness
-- statement:
--   Definitions and structural lemmas for Measure Smoothness, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/MeasureSmoothness.lean

import Definitions.Def_BKAR_CubePartition_MeasurePartition
import Definitions.Def_BKAR_PartialDerivSymmetry
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
end Forest
end BKAR


