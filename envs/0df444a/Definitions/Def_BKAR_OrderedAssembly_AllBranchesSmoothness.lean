-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
-- name    : BKAR_OrderedAssembly_AllBranchesSmoothness
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:05:13.170415+00:00
-- url     : https://prove2.me/theorems/c2934be2-e903-4aa2-8373-397bdc0630dd
-- title:
--   All Branches Smoothness
-- statement:
--   Definitions and structural lemmas for All Branches Smoothness, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
end BKARContDiff
end BKAR


