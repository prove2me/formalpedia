-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterPrime
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:21.121672+00:00
-- url     : https://prove2.me/theorems/d70efd2d-8a72-4716-959f-32df6f312228
-- title:
--   Height Orbit Center Prime
-- statement:
--   Definitions and structural lemmas for Height Orbit Center Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenterPrime.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
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
open ReciprocityTheory.ChartRestriction.G NumberField
def OrbitCenterPrime.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x → ∀ v : FinitePlace (coordField x), (orbitCenter x v).IsPrime
example : BlockNonzero samplePoint := samplePoint_blockNonzero
end GroundTheory.Heights₂.Heights


