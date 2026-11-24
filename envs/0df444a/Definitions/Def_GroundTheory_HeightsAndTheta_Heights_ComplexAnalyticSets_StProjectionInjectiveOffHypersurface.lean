-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionInjectiveOffHypersurface
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StProjectionInjectiveOffHypersurface
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:32.681802+00:00
-- url     : https://prove2.me/theorems/26bac0fd-d8b1-4ef7-b577-9d36e85c07ef
-- title:
--   St Projection Injective Off Hypersurface
-- statement:
--   Definitions and structural lemmas for St Projection Injective Off Hypersurface, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StProjectionInjectiveOffHypersurface.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
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
def ProjectionInjectiveOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 →
      ∃ W : Set (σ → ℂ), IsOpen W ∧ z ∈ W ∧
        ∃ A : (σ → ℂ) →L[ℂ] (Fin k → ℂ), Set.InjOn A (zeroSetIn I ∩ W)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


