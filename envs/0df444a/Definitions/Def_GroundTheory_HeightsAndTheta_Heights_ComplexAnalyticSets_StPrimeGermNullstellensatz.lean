-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPrimeGermNullstellensatz
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:48.567632+00:00
-- url     : https://prove2.me/theorems/6f796a1e-b9eb-492f-92de-c7c9cd7226a0
-- title:
--   St Prime Germ Nullstellensatz
-- statement:
--   Definitions and structural lemmas for St Prime Germ Nullstellensatz, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StPrimeGermNullstellensatz.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
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
noncomputable def holGermIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) {k : ℕ} (f : Fin k → (σ → ℂ) → ℂ) : Ideal (holGerms w) :=
  Ideal.span {φ | ∃ i, (φ : Germ (𝓝 w) ℂ) = (f i : Germ (𝓝 w) ℂ)}
def PrimeGermNullstellensatz.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (p : Fin k → (σ → ℂ) → ℂ) (g : (σ → ℂ) → ℂ),
    (∀ i, AnalyticAt ℂ (p i) w) → AnalyticAt ℂ g w → (holGermIdeal w p).IsPrime →
    (∀ᶠ z in 𝓝 w, (∀ i, p i z = 0) → g z = 0) →
    ∃ h : Fin k → (σ → ℂ) → ℂ, (∀ i, AnalyticAt ℂ (h i) w) ∧ ∀ᶠ z in 𝓝 w, g z = ∑ i, h i z * p i z
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


