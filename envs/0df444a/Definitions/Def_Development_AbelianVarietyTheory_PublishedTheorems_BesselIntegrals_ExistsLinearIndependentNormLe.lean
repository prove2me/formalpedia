-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_ExistsLinearIndependentNormLe
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_BesselIntegrals_ExistsLinearIndependentNormLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:53.078222+00:00
-- url     : https://prove2.me/theorems/3da2e891-1b5b-43c5-9d02-543ba569043c
-- title:
--   Exists Linear Independent Norm Le
-- statement:
--   Definitions and structural lemmas for Exists Linear Independent Norm Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/BesselIntegrals/ExistsLinearIndependentNormLe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
namespace GlobalTheory.Published
def SuccMinTransference : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (i : ℕ), 1 ≤ i → i ≤ n → succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n
namespace SuccMinTransference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
end SuccMinTransference
example : succMin (1 : Submodule ℤ ℝ) 1 * succMin (dualLattice (1 : Submodule ℤ ℝ)) (1 - 1 + 1) =
    ((1 : ℕ) : ℝ) := by
  have := minNorm_one_real
  rw [minNorm] at this
  simp [dualLattice_one_real, this]
example (h : SuccMinTransference) (n : ℕ) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ n) :
    let L := span ℤ (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
    succMin L i * succMin (dualLattice L) (n - i + 1) ≤ n :=
  h n _ i h1 hi
end GlobalTheory.Published


