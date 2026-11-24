-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalBoundedQuotient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:50.638829+00:00
-- url     : https://prove2.me/theorems/6a30436d-21b3-4bea-8793-9ff7caf76ad0
-- title:
--   St Normal Bounded Quotient
-- statement:
--   Definitions and structural lemmas for St Normal Bounded Quotient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalBoundedQuotient.lean

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
def NormalBoundedQuotient.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    Bornology.IsBounded ((fun z => F z / G z) '' ((zeroSetIn I ∩ N) \ {z | G z = 0})) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


