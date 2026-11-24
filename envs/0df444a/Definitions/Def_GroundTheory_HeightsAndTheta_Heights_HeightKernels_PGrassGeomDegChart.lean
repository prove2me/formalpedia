-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassGeomDegChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:07.398514+00:00
-- url     : https://prove2.me/theorems/a659f722-4d4e-4350-9f61-a728a914e61d
-- title:
--   PGrass Geom Deg Chart
-- statement:
--   Definitions and structural lemmas for PGrass Geom Deg Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassGeomDegChart.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassGeomDegChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheetA
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Matrix
noncomputable section
namespace GrassmannianGeometricDegreeChart
variable {n : ℕ}
def single1 (c : Fin (1 + n)) : PlIdx 1 n := ⟨{c}, Finset.card_singleton c⟩
def a0 : Σ _ : Fin 1, PlIdx 1 n := ⟨0, single1 (Fin.castAdd n 0)⟩
def chartPt (z : (Σ _ : Fin 1, PlIdx 1 n) → ℂ) : Fin 1 → Matrix (Fin 1) (Fin n) ℂ :=
  fun _ _ b => z ⟨0, single1 (Fin.natAdd 1 b)⟩ / z a0
def blockLift (x : PlIdx 1 n → ℂ) : (Σ _ : Fin 1, PlIdx 1 n) → ℂ := fun p => x p.2
end GrassmannianGeometricDegreeChart
end
end GroundTheory.Heights₂.Heights


