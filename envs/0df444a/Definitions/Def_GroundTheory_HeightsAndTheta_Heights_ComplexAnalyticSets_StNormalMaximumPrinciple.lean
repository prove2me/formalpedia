-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:01.547699+00:00
-- url     : https://prove2.me/theorems/c0c6c2ce-9036-4a4b-9421-419c34619aba
-- title:
--   St Normal Maximum Principle
-- statement:
--   Definitions and structural lemmas for St Normal Maximum Principle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalMaximumPrinciple.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
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
open MvPolynomial Topology
def NormalMaximumPrinciple.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → U ∈ 𝓝 w →
    HolomorphicOnSubset g (zeroSetIn I ∩ U) → (∀ z ∈ zeroSetIn I ∩ U, ‖g z‖ ≤ ‖g w‖) →
    ∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → g z = g w
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


