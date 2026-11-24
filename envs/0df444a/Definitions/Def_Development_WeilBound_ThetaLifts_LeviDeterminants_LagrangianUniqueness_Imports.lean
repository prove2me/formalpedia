-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
-- name    : Development_WeilBound_ThetaLifts_LeviDeterminants_LagrangianUniqueness_Imports
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:05:40.098626+00:00
-- url     : https://prove2.me/theorems/bb437ca3-a2ee-4fa4-af6b-3aaeb8d7b443
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LeviDeterminants/LagrangianUniqueness/Imports.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM Filter Topology
open scoped Classical
noncomputable section
namespace PositivityTheory.ThKF0.FinLine
variable {G : Type} [AddCommGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]
def ind (U : OpenAddSubgroup G) (a : G) : G → ℂ := fun x => if x - a ∈ U then 1 else 0
variable {U₀ : OpenAddSubgroup G} (h₀ : IsCompact (U₀ : Set G)) {P : Set G} {l : (G → ℂ) →ₗ[ℂ] ℂ}
end PositivityTheory.ThKF0.FinLine


