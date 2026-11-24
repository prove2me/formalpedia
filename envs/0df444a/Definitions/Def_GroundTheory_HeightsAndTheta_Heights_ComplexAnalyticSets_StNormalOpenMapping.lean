-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalOpenMapping
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:02.063309+00:00
-- url     : https://prove2.me/theorems/48c99bdf-226b-472d-80b1-41c7fd1b7130
-- title:
--   St Normal Open Mapping
-- statement:
--   Definitions and structural lemmas for St Normal Open Mapping, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StNormalOpenMapping.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
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
open MvPolynomial
def NormalOpenMapping.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
    ∃ O : Set (σ → ℂ), IsOpen O ∧ φ '' U = zeroSetIn I ∩ O
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


