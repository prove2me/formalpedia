-- Prove2me | Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
-- name    : BKAR_OrderedAssembly_ForestIndexCube
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:02:07.561264+00:00
-- url     : https://prove2.me/theorems/c6eabf86-9db0-4b22-936f-c38492f417a7
-- title:
--   Forest Index Cube
-- statement:
--   Definitions and structural lemmas for Forest Index Cube, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/ForestIndexCube.lean

import Definitions.Def_BKAR_OrderedAssembly_CubeFold
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace ForestIndex
variable {V : Type*} [Fintype V] [DecidableEq V]
def cubeContribution (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  by
    classical
    exact
      if hchoices : Nonempty (Forest.ActiveExtensionChoice V) then
        (Forest.canonicalGrownForestForSupport (Classical.choice hchoices) I)
          |>.cubeContribution ρ
      else
        0
end ForestIndex
end BKAR


