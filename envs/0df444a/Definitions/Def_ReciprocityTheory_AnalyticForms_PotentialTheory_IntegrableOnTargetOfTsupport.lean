-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:23.148269+00:00
-- url     : https://prove2.me/theorems/2efd4bb9-95cf-4334-aec3-8fa2091789d4
-- title:
--   Integrable On Target Of Tsupport
-- statement:
--   Definitions and structural lemmas for Integrable On Target Of Tsupport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegrableOnTargetOfTsupport.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas
open scoped ContDiff
noncomputable section
section helpers
variable {e : ℕ} {X : Type} [TopologicalSpace X]
end helpers
def MIntLocalizeStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    ∀ (j : Fin A.n) (g : X → ℝ), tsupport g ⊆ (A.chart j).source → MIntegrable A Φ g →
      integralWith A P Φ g =
        ∫ y in (A.chart j).target, g ((A.chart j).symm y) * locDens A Φ j y
def MIntegrableMulStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (g c : X → ℝ), MIntegrable A Φ g → Continuous c → MIntegrable A Φ (fun x => c x * g x)
end
end ReciprocityTheory.AnForm.M


