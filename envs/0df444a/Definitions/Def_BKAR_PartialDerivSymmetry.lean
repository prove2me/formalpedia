-- Prove2me | Definitions.Def_BKAR_PartialDerivSymmetry
-- name    : BKAR_PartialDerivSymmetry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:48:20.52346+00:00
-- url     : https://prove2.me/theorems/68c1fde4-1e88-5cf3-9e7c-4f9483d8f47b
-- title:
--   Partial Deriv Symmetry
-- statement:
--   Definitions and structural lemmas for Partial Deriv Symmetry, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
set_option autoImplicit false
open scoped ContDiff
namespace BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}
end BKARContDiff
namespace Forest
variable (F : Forest V)
variable {ρ : (Edge V → ℝ) → ℝ}
end Forest
end BKAR


