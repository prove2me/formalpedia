-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalGermIntegrallyClosed
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:41.34167+00:00
-- url     : https://prove2.me/theorems/aa7e2609-4b08-4dfe-b882-91a61458e976
-- title:
--   St Normal Germ Integrally Closed
-- statement:
--   Definitions and structural lemmas for St Normal Germ Integrally Closed, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalGermIntegrallyClosed.lean

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
def NormalGermIntegrallyClosed.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (N : Set (σ → ℂ))
    (F G : (σ → ℂ) → ℂ) (d : ℕ) (a : Fin d → (σ → ℂ) → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I → IsOpen N → w ∈ N →
    DifferentiableOn ℂ F N → DifferentiableOn ℂ G N → (∀ j, DifferentiableOn ℂ (a j) N) →
    ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → G z = 0) →
    (∀ z ∈ (zeroSetIn I ∩ N) \ {z | G z = 0},
      F z ^ d + ∑ j, a j z * F z ^ (j : ℕ) * G z ^ (d - (j : ℕ)) = 0) →
    ∃ V : Set (σ → ℂ), IsOpen V ∧ w ∈ V ∧ ∃ H : (σ → ℂ) → ℂ, DifferentiableOn ℂ H V ∧
      ∀ z ∈ zeroSetIn I ∩ V, F z = G z * H z
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


