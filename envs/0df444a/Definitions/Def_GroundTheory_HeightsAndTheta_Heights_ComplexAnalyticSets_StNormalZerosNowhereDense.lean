-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalZerosNowhereDense
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:37.852584+00:00
-- url     : https://prove2.me/theorems/2bc255cd-af7a-42b3-8eb4-0a25a5736d37
-- title:
--   St Normal Zeros Nowhere Dense
-- statement:
--   Definitions and structural lemmas for St Normal Zeros Nowhere Dense, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalZerosNowhereDense.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
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
def NormalZerosNowhereDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ G N → ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    ∃ U : Set (σ → ℂ), IsOpen U ∧ w ∈ U ∧ U ⊆ N ∧
      ∀ z ∈ zeroSetIn I ∩ U, ∀ V ∈ 𝓝 z, ∃ x ∈ zeroSetIn I ∩ V, G x ≠ 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


