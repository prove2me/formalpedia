-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AnalyticGerm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:14.458613+00:00
-- url     : https://prove2.me/theorems/d22299f7-8027-4f8a-8796-c3ba38f1aadc
-- title:
--   Analytic Germ
-- statement:
--   Definitions and structural lemmas for Analytic Germ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/AnalyticGerm.lean

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
def IsAnalyticNear {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  ∃ (N : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
    (∀ i, AnalyticOnNhd ℂ (f i) N) ∧ X ∩ N = {z | z ∈ N ∧ ∀ i, f i z = 0}
def GermIrreducibleAt {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  w ∈ X ∧ ∀ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∨ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


