-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartRing
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:07.390816+00:00
-- url     : https://prove2.me/theorems/86bbfe29-070a-477d-bb9e-f1e1718d9328
-- title:
--   Height Orbit Chart Ring
-- statement:
--   Definitions and structural lemmas for Height Orbit Chart Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitChartRing.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChart
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
def OrbitChartRing.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (c : (k : ι) → Fin (n k + 1)), (∀ k, x k (c k) ≠ 0) →
      Algebra.FiniteType ℤ (chartRing x c) ∧ IsFractionRing (chartRing x c) (ratioField x)
example : ∀ k, samplePoint k ((fun _ ↦ 0) k) ≠ 0 := fun _ ↦ by simp [samplePoint]
end GroundTheory.Heights₂.Heights


