-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushLocalStatement
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_PushLocalStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:39:25.688684+00:00
-- url     : https://prove2.me/theorems/64a84f1d-8aa0-4a77-a79d-8e03941c05f8
-- title:
--   Push Local Statement
-- statement:
--   Definitions and structural lemmas for Push Local Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/PushLocalStatement.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushBForward
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
def PushLocalStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → ∀ (q : X → Fin e → ℂ) (V : Set X),
    IsOpen V → Set.InjOn q V → (∀ i, A.HoloOn V (fun x => q x i)) →
    (∀ x ∈ V, ∀ j, x ∈ (A.chart j).source →
      LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) →
    ∀ g : X → ℝ, tsupport g ⊆ V → MIntegrable A Φ g →
      mInt A Φ g = ∫ y in q '' V, ∑ᶠ x ∈ q ⁻¹' {y} ∩ V, g x * pushDens A Φ q x
end
end ReciprocityTheory.AnForm.M


