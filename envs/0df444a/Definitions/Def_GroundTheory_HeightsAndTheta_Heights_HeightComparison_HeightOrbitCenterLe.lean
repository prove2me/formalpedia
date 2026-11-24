-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:09.277721+00:00
-- url     : https://prove2.me/theorems/9e9fb39a-9003-4ac8-98c7-8d22adefd7b2
-- title:
--   Height Orbit Center Le
-- statement:
--   Definitions and structural lemmas for Height Orbit Center Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenterLe.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
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
def OrbitCenterLe.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (v : FinitePlace (coordField x)) (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
    Geo.IsMultiHomog (ι := blockIdx n) F d →
      v (evalCone (coordVec x) F) ≤ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k
example : Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 0) 1) 1 :=
  (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _)
end GroundTheory.Heights₂.Heights


