-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:26.678583+00:00
-- url     : https://prove2.me/theorems/b9bd90a0-03a0-4a7a-b9af-f14c50851f23
-- title:
--   Height Orbit Degree
-- statement:
--   Definitions and structural lemmas for Height Orbit Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09

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
open ReciprocityTheory.ChartRestriction.G
def OrbitDegree.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → 0 < Geo.degC (ι := blockIdx n) (orbitIdeal x)
example : BlockNonzero samplePoint := samplePoint_blockNonzero
end GroundTheory.Heights₂.Heights


