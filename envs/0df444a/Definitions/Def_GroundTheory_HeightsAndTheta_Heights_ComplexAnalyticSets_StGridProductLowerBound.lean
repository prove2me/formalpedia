-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGridProductLowerBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:06.614825+00:00
-- url     : https://prove2.me/theorems/98edf701-4a13-4d8e-ae5d-f9eda412b8cd
-- title:
--   St Grid Product Lower Bound
-- statement:
--   Definitions and structural lemmas for St Grid Product Lower Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGridProductLowerBound.lean

import Mathlib
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
open Topology
def GridProductLowerBound.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (N : ℕ) (Z : Set (σ → ℂ)) (z₀ : σ → ℂ),
    Bornology.IsBounded Z → z₀ ∉ closure Z →
    ∃ μ : ℝ, 0 < μ ∧ ∃ U ∈ 𝓝 z₀, ∀ z ∈ U, ∀ s : Finset (σ → ℂ), (↑s : Set (σ → ℂ)) ⊆ Z → s.card ≤ N →
      ∃ u : σ → Fin (N + 1), μ ≤ ‖∏ x ∈ s, ∑ i, ((u i : ℕ) : ℂ) * (z i - x i)‖
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


