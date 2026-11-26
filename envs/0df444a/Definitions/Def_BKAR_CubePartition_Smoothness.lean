-- Prove2me | Definitions.Def_BKAR_CubePartition_Smoothness
-- name    : BKAR_CubePartition_Smoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:51:30.528473+00:00
-- url     : https://prove2.me/theorems/51b3a149-3bbe-5d21-993c-8bb7cd5f4a8a
-- title:
--   Smoothness
-- statement:
--   Definitions and structural lemmas for Smoothness, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
set_option autoImplicit false
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace EdgeExtension
variable {F F' : Forest V} {e : Edge V}
end EdgeExtension
end Forest
namespace BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
variable {F F' : Forest V} {e : Edge V}
end BKARContDiff
end BKAR


