-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseHolomorphic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseHolomorphic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:15.955406+00:00
-- url     : https://prove2.me/theorems/2ebf27c3-c01e-44ae-b2a5-3d6709fda6d4
-- title:
--   St Branch Inverse Holomorphic
-- statement:
--   Definitions and structural lemmas for St Branch Inverse Holomorphic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StBranchInverseHolomorphic.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchContainsNormalPoint
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
def BranchInverseHolomorphic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (h : MvPolynomial σ ℂ) (w : σ → ℂ)
    (k : ℕ) (r : ℝ) (φ : (Fin k → ℂ) → σ → ℂ) (B : Set (σ → ℂ)),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → h ∉ I → w ∈ zeroSetIn I →
    DifferentiableOn ℂ φ (Metric.ball 0 r) → Set.InjOn φ (Metric.ball 0 r) →
    Set.MapsTo φ (Metric.ball 0 r) (zeroSetIn I) → B ∈ 𝓝 w →
    (zeroSetIn I ∩ B) \ {z | eval z h = 0} ⊆ φ '' Metric.ball 0 r →
    ∃ ψ : (σ → ℂ) → Fin k → ℂ, HolomorphicOnSubset ψ (φ '' Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball 0 r, ψ (φ t) = t
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


