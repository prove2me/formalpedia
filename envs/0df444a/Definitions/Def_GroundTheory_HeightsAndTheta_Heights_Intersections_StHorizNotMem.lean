-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StHorizNotMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:07:33.554462+00:00
-- url     : https://prove2.me/theorems/98f90b0a-de1e-4ce7-9040-a60ad0c6babc
-- title:
--   St Horiz Not Mem
-- statement:
--   Definitions and structural lemmas for St Horiz Not Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StHorizNotMem.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
def HorizNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (s s' : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P d → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    W ∈ divSupp P s → IsHorizontal W → s' ∉ W
end GroundTheory.Heights₂.Heights.Inter


