-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularLocusIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:17.060593+00:00
-- url     : https://prove2.me/theorems/ac80681f-154e-4e91-8765-036e1a60ea04
-- title:
--   St Regular Locus Identity
-- statement:
--   Definitions and structural lemmas for St Regular Locus Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRegularLocusIdentity.lean

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
def RegularLocusIdentity.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)), I.IsPrime →
    ∃ h : MvPolynomial σ ℂ, h ∉ I ∧ ∀ z ∈ zeroSetIn I, eval z h ≠ 0 → ∀ W ∈ 𝓝 z,
      ∃ V : Set (σ → ℂ), IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        ∀ F : (σ → ℂ) → ℂ, AnalyticOnNhd ℂ F V →
          (∃ y ∈ zeroSetIn I ∩ V, ∀ᶠ u in 𝓝 y, u ∈ zeroSetIn I → F u = 0) →
            ∀ u ∈ zeroSetIn I ∩ V, F u = 0
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


