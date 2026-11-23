-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_BasicCycleRangeLastCastSucc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:13.420299+00:00
-- url     : https://prove2.me/theorems/dfeaafd0-a1c7-446d-9616-0a72b1d2dc88
-- title:
--   Basic Cycle Range Last Cast Succ
-- statement:
--   Definitions and structural lemmas for Basic Cycle Range Last Cast Succ, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/BasicCycleRangeLastCastSucc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliCentralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
def permIns {p : ℕ} (i : Fin (p + 1)) (τ : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  i.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, τ)
section Ring
variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰] {n : ℕ} (E : Fin n → Fin n → 𝒰)
end Ring
section Module
end Module
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli


