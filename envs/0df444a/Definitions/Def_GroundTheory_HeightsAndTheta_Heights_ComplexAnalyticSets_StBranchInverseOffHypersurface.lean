-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseOffHypersurface
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseOffHypersurface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:59:43.538651+00:00
-- url     : https://prove2.me/theorems/d6945116-4ae8-44ad-a1f7-e9929b763bd4
-- title:
--   St Branch Inverse Off Hypersurface
-- statement:
--   Definitions and structural lemmas for St Branch Inverse Off Hypersurface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchInverseOffHypersurface.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
def BranchInverseOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h' : MvPolynomial σ ℂ, h' ∉ I ∧
      ∀ (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → σ → ℂ) (ψ : (σ → ℂ) → Fin k → ℂ),
        IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
        (∀ t ∈ U, ψ (φ t) = t) →
        HolomorphicOnSubset ψ ((φ '' U) \ {z | eval z h' = 0})
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


