-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermComponents
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:19.304252+00:00
-- url     : https://prove2.me/theorems/6b3fd259-f87e-410b-998a-52ae74ec253f
-- title:
--   PAnalytic Germ Components
-- statement:
--   Definitions and structural lemmas for PAnalytic Germ Components, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermComponents.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
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
namespace AnalyticGermComponents
variable {σ : Type} [Fintype σ]
def vanishingIdeal (X : Set (σ → ℂ)) (w : σ → ℂ) : Ideal (holGerms w) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, (f : Germ (𝓝 w) ℂ) = (φ : Germ (𝓝 w) ℂ) ∧ ∀ᶠ z in 𝓝 w, z ∈ X → f z = 0}
  add_mem' := by
    rintro a b ⟨f, hf, hf0⟩ ⟨g, hg, hg0⟩
    refine ⟨f + g, ?_, ?_⟩
    · show ((f + g : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (a : Germ (𝓝 w) ℂ) + (b : Germ (𝓝 w) ℂ)
      rw [← hf, ← hg]
      rfl
    · filter_upwards [hf0, hg0] with z h1 h2 hz
      simp [h1 hz, h2 hz]
  zero_mem' := ⟨0, rfl, Eventually.of_forall fun _ _ => rfl⟩
  smul_mem' := by
    rintro c a ⟨f, hf, hf0⟩
    obtain ⟨h, -, hh⟩ := c.2
    refine ⟨h * f, ?_, ?_⟩
    · show ((h * f : (σ → ℂ) → ℂ) : Germ (𝓝 w) ℂ) = (c : Germ (𝓝 w) ℂ) * (a : Germ (𝓝 w) ℂ)
      rw [← hh, ← hf]
      rfl
    · filter_upwards [hf0] with z h1 hz
      simp [h1 hz]
end AnalyticGermComponents
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


