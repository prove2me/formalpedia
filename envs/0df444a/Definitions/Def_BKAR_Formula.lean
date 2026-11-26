-- Prove2me | Definitions.Def_BKAR_Formula
-- name    : BKAR_Formula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:02:50.694509+00:00
-- url     : https://prove2.me/theorems/edfdab50-e330-5097-94e7-602749904af6
-- title:
--   Formula
-- statement:
--   Definitions and structural lemmas for Formula, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Formula.lean

import Definitions.Def_BKAR_OrderedAssembly_ForestIndexCube
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
namespace BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
def grownForestCubeSectorSum
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I => Finset.sum (Forest.edgeSetOrders I.edges).attach
      (fun order =>
        (Forest.grownForestForSupportOrder choices I order).orderedCubeSectorContribution
          order.val ρ))
def canonicalGrownForestCubeContributionSum
    (choices : Forest.ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I =>
      (Forest.canonicalGrownForestForSupport choices I).cubeContribution ρ)
end BKAR


