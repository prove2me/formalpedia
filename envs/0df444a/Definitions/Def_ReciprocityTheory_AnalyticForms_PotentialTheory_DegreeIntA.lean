-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
-- name    : ReciprocityTheory_AnalyticForms_PotentialTheory_DegreeIntA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:37:51.542797+00:00
-- url     : https://prove2.me/theorems/4dc2531b-e5fd-4ba1-8913-d09281fb898e
-- title:
--   Degree Int A
-- statement:
--   Definitions and structural lemmas for Degree Int A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/DegreeIntA.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PotentialContDiffAt
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
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def DIChartDens (A : FinHolAtlas e X) (D : Fin A.n → (Fin e → ℂ) → ℝ) : Prop :=
  ∀ a b, ∀ z ∈ (A.chart a).target, (A.chart a).symm z ∈ (A.chart b).source →
    D a z = D b (A.chart b ((A.chart a).symm z)) *
      ‖LinearMap.det (fderiv ℂ (A.chart b ∘ (A.chart a).symm) z :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ))‖ ^ 2
end
end ReciprocityTheory.AnForm.M


