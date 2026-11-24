-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:38.314835+00:00
-- url     : https://prove2.me/theorems/e210b755-26b4-44ac-ad2b-aa32c66e1d0d
-- title:
--   St Power Sums Esymm Analytic
-- statement:
--   Definitions and structural lemmas for St Power Sums Esymm Analytic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPowerSumsEsymmAnalytic.lean

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
open Topology Filter
noncomputable section
def PowerSumsEsymmAnalytic.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (V : Set (σ → ℂ)) (d : ℕ) (Z : (σ → ℂ) → Multiset ℂ),
    IsOpen V → (∀ z ∈ V, Multiset.card (Z z) = d) →
    (∀ k, 1 ≤ k → k ≤ d → AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) V) →
    ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) V
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


