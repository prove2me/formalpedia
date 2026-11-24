-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
-- name    : GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsPushForwardOpen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:10:56.840481+00:00
-- url     : https://prove2.me/theorems/52ec27d3-7d40-47f4-af31-3549bf77df57
-- title:
--   Statements Push Forward Open
-- statement:
--   Definitions and structural lemmas for Statements Push Forward Open, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/StatementsPushForwardOpen.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Targets
open MeasureTheory ReciprocityTheory.AnForm.M
def PushForwardOpen.Statement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (O : Set X),
    IsOpen O →
    (∀ x ∈ O, ∀ j, x ∈ (A.chart j).source →
      AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧
        LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    (∀ j, ∀ᵐ u, u ∈ (A.chart j).target → (A.chart j).symm u ∉ O → locDens A Φ j u = 0) →
    (∀ᵐ y, (q ⁻¹' {y} ∩ O).Finite) →
    ∀ g : X → ℝ, MIntegrable A Φ g →
      Integrable (fun y => ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x) ∧
        mInt A Φ g = ∫ y, ∑ᶠ x ∈ q ⁻¹' {y} ∩ O, g x * pushDens A Φ q x
end GroundTheory.Heights₂.Heights.Targets


