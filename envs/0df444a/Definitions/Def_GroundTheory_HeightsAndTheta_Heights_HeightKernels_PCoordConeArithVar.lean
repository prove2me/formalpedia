-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCoordConeArithVar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:37.745368+00:00
-- url     : https://prove2.me/theorems/e20642f6-c251-4fd5-952b-6d38bd9e388f
-- title:
--   PCoord Cone Arith Var
-- statement:
--   Definitions and structural lemmas for PCoord Cone Arith Var, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PCoordConeArithVar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PConeTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
namespace CoordinateConeArithVar
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω :=
  fun p ↦ y p / y ⟨p.1, c p.1⟩
def scaleT (a : K → Ω) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω :=
  aeval fun k ↦ C (a k) * X k
abbrev ratioField [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : IntermediateField ℚ Ω :=
  IntermediateField.adjoin ℚ (coneRatios y c)
def ratioPtL [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → ratioField y c :=
  fun p ↦ ⟨ratioPt y c p, IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩⟩
end CoordinateConeArithVar
end
end GroundTheory.Heights₂.Heights


