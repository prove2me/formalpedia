-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:41.162452+00:00
-- url     : https://prove2.me/theorems/089ea12b-d2b9-4768-a49e-30256ae5b9d6
-- title:
--   Height Orbit Center
-- statement:
--   Definitions and structural lemmas for Height Orbit Center, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenter.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
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
noncomputable section
variable {ι : Type} {n : ι → ℕ}
def ratioField (x : Cone n (AlgebraicClosure ℚ)) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ
    (Set.range fun p : (k : ι) × Fin (n k + 1) × Fin (n k + 1) ↦ x p.1 p.2.1 / x p.1 p.2.2)
theorem div_mem_ratioField (x : Cone n (AlgebraicClosure ℚ)) (k : ι) (i j : Fin (n k + 1)) :
    x k i / x k j ∈ ratioField x :=
  IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i, j⟩, rfl⟩
variable [Fintype ι]
instance (x : Cone n (AlgebraicClosure ℚ)) : FiniteDimensional ℚ (ratioField x) :=
  IntermediateField.finiteDimensional_adjoin fun y _ ↦ isIntegral_algebraicClosure_rat y
instance (x : Cone n (AlgebraicClosure ℚ)) : NumberField (ratioField x) := {}
def orbitCenter (x : Cone n (AlgebraicClosure ℚ)) (v : FinitePlace (coordField x)) :
    Ideal (MvPolynomial (Coord n) ℤ) :=
  Ideal.span {F | ∃ d : ι → ℕ, Geo.IsMultiHomog (ι := blockIdx n) F d ∧
    v (evalCone (coordVec x) F) < ∏ k, (⨆ i, v (coordVec x k i)) ^ d k}
variable [DecidableEq ι]
example : (1 / 2 : AlgebraicClosure ℚ) ∈ ratioField samplePoint := by
  convert div_mem_ratioField samplePoint () 0 1 using 1
  simp [samplePoint]
end
end GroundTheory.Heights₂.Heights


