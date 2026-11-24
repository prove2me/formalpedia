-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:23:46.30236+00:00
-- url     : https://prove2.me/theorems/d65a9e71-9d8f-4383-916e-7a87426e3719
-- title:
--   PGraph Isometric
-- statement:
--   Definitions and structural lemmas for PGraph Isometric, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometric.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PChangeOfModel
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
set_option linter.unusedSectionVars false
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
namespace GraphIsometric
section Divisor
variable {K : Type*} [Fintype K] {κ : K → Type*} [∀ k, Fintype (κ k)]
end Divisor
section Graph
variable {K : Type} [Fintype K] {ι ι₂ : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι₂ k)]
def num (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, rename inlV (linForm A ⟨k, j k⟩) ^ (a k).toNat * X (inrV ⟨k, j k⟩) ^ (-a k).toNat
def den (A : ∀ k, ι₂ k → ι k → ℤ) (j : ∀ k, ι₂ k) (a : K → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, X (inrV ⟨k, j k⟩) ^ (a k).toNat * rename inlV (linForm A ⟨k, j k⟩) ^ (-a k).toNat
end Graph
end GraphIsometric
end GroundTheory.Heights₂.Heights.HilbertSamuel


