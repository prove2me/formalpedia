-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:00.9014+00:00
-- url     : https://prove2.me/theorems/d086f718-b090-483a-8790-694356d745df
-- title:
--   Inter Bridge H
-- statement:
--   Definitions and structural lemmas for Inter Bridge H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterBridgeH.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeG
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.M
variable {e : ℕ} {X : Type} [TopologicalSpace X]
def goodT (A : FinHolAtlas e X) (q : X → Fin e → ℂ) (j : Fin A.n) : Set (Fin e → ℂ) :=
  {u | u ∈ (A.chart j).target ∧ AnalyticAt ℂ (q ∘ (A.chart j).symm) u ∧
    LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) u : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0}
end ReciprocityTheory.ChartRestriction.G.Geo


