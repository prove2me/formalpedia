-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsSemidirectHaar
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T03:50:44.880403+00:00
-- url     : https://prove2.me/theorems/7263828b-fe7c-4762-9f5c-e5ab29c8b359
-- title:
--   Statements Semidirect Haar
-- statement:
--   Definitions and structural lemmas for Statements Semidirect Haar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StatementsSemidirectHaar.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsLineStabHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory
open scoped ENNReal NNReal
noncomputable section
def SemidirectHaar.Statement (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] : Prop :=
  ∀ (P H : Subgroup G), IsClosed (P : Set G) → IsClosed (H : Set G) → H ≤ P →
    ∀ (τ : T →* G) (β : P → T) (δ : T → ℝ≥0), Continuous τ → Continuous β → Continuous δ →
    (∀ t, τ t ∈ P) → (∀ t, ∀ x ∈ H, τ t * x * (τ t)⁻¹ ∈ H) → (∀ t, τ t ∈ H → t = 1) →
    (∀ p : P, (p : G) * (τ (β p))⁻¹ ∈ H) →
    ∀ (μ : Measure P) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (ρ : Measure T) [ρ.IsHaarMeasure],
    (∀ (t : T) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂ν = δ t * ∫⁻ x, f x ∂ν) →
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ p, φ p ∂μ = c * ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


