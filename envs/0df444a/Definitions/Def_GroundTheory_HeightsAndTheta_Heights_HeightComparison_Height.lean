-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_Height
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:25.309242+00:00
-- url     : https://prove2.me/theorems/7f7d8eae-0a3d-4db1-99de-6db56f91dafa
-- title:
--   Height
-- statement:
--   Definitions and structural lemmas for Height, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/Height.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightRecR
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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace HermLine
def standardPow (m : ι → ℕ) : HermLine n where
  deg k := m k
  metric z := ∏ k, l2Norm (z k) ^ m k
  metric_pos z hz := Finset.prod_pos fun k _ ↦ pow_pos (vectorL2Norm_pos (hz k)) _
  metric_smul c z _ _ := by
    simp only [vectorL2Norm_const_mul, mul_pow, Finset.prod_mul_distrib, zpow_natCast]
  metric_smooth := contDiffOn_prod fun k _ ↦ (contDiffOn_l2Norm_block k).pow _
end HermLine
def HeightAsIntersection.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι] (n : ι → ℕ)
    (II : Ideal (MvPolynomial (Coord n) ℤ) → (m : ℕ) → (Fin m → Geo.HermLine (blockIdx n)) → ℝ),
    Geo.IsIntersectionFamily II → ∀ (A : HermLine n) (x : Cone n (AlgebraicClosure ℚ)),
    BlockNonzero x →
    height A x = II (orbitIdeal x) 1 ![A.toGeo] / Geo.degC (ι := blockIdx n) (orbitIdeal x)
end
end GroundTheory.Heights₂.Heights


