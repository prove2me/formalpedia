-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRueckertNullstellensatz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:31:15.42133+00:00
-- url     : https://prove2.me/theorems/86864329-df8c-4f8b-a237-f19719897c7e
-- title:
--   St Rueckert Nullstellensatz
-- statement:
--   Definitions and structural lemmas for St Rueckert Nullstellensatz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StRueckertNullstellensatz.lean

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
def RueckertNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (f i) w) → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, (∀ i, f i z = 0) → g z = 0) →
    ∃ (m : ℕ) (h : Fin k → (σ → ℂ) → ℂ), 0 < m ∧ (∀ i, AnalyticAt ℂ (h i) w) ∧
      ∀ᶠ z in 𝓝 w, g z ^ m = ∑ i, h i z * f i z
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


