-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometricForms
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:14.502807+00:00
-- url     : https://prove2.me/theorems/f5de674e-1e34-452f-b774-657e93f0c298
-- title:
--   PGraph Isometric Forms
-- statement:
--   Definitions and structural lemmas for PGraph Isometric Forms, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PGraphIsometricForms.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphIsometric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PGraphChangeOfModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGraphIsometricForms
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
namespace GraphIsometricForms
section Extend
variable {K K₂ M : Type*} [Zero M]
end Extend
section Graph
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
def num (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, rename inlV (g ⟨k, j k⟩) ^ (a k).toNat * X (inrV ⟨k, j k⟩) ^ (-a k).toNat
def den (g : (Σ k, ι₂ k) → MRing ι) (j : ∀ k, ι₂ k) (a : K₂ → ℤ) : MRing (Sum.elim ι ι₂) :=
  ∏ k, X (inrV ⟨k, j k⟩) ^ (a k).toNat * rename inlV (g ⟨k, j k⟩) ^ (-a k).toNat
end Graph
end GraphIsometricForms
end GroundTheory.Heights₂.Heights.HilbertSamuel


