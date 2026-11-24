-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:40.070876+00:00
-- url     : https://prove2.me/theorems/5d3272fc-85d1-4854-9358-fd639bd4d7e7
-- title:
--   St Local Trace
-- statement:
--   Definitions and structural lemmas for St Local Trace, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StLocalTrace.lean

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
def LocalTrace.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (U : Set (σ → ℂ))
    (g : (σ → ℂ) → ℂ),
    I.IsPrime → w ∈ zeroSetIn I → U ∈ 𝓝 w → HolomorphicOnSubset g (zeroSetIn I ∩ U) →
    ∃ (k : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin k → ℂ)) (B : Set (σ → ℂ)) (D : Set (Fin k → ℂ)) (m : ℕ)
      (T : (Fin k → ℂ) → ℂ),
      IsOpen B ∧ w ∈ B ∧ B ⊆ U ∧ IsOpen D ∧ A w ∈ D ∧
      (∀ z ∈ zeroSetIn I ∩ B, A z = A w → z = w) ∧ DifferentiableOn ℂ T D ∧
      ∀ y ∈ D, ∃ x : Fin m → σ → ℂ, (∀ j, x j ∈ zeroSetIn I ∩ B ∧ A (x j) = y) ∧
        (∀ z ∈ zeroSetIn I ∩ B, A z = y → z ∈ Set.range x) ∧ T y = ∑ j, g (x j)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


