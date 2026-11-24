-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:42.492356+00:00
-- url     : https://prove2.me/theorems/33908667-f15c-4851-acc8-10dffb4d5d9e
-- title:
--   Statements Grass Geom Deg Chart
-- statement:
--   Definitions and structural lemmas for Statements Grass Geom Deg Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsGrassGeomDegChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsChartMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo Matrix
open scoped ComplexOrder
noncomputable section
def GrassGeomDegChart.Statement : Prop :=
  ∀ n : ℕ, ∃ B : Matrix (PlIdx 1 n) (Fin (n + 1)) ℂ, Function.Bijective B.mulVec ∧
    geomDeg (grassIdeal 1 1 n) (fsMulti (plBlocks 1 1 n)) n = chartMass (Bᴴ * B)
example : Ideal (MRing (plBlocks 1 1 2)) × HermLine (plBlocks 1 1 2) :=
  ⟨grassIdeal 1 1 2, fsMulti (plBlocks 1 1 2)⟩
example (n : ℕ) : Fintype.card (PlIdx 1 n) = n + 1 := by
  simp [PlIdx, Fintype.card_subtype, Finset.card_powersetCard, add_comm]
end
end GroundTheory.Heights₂.Heights


