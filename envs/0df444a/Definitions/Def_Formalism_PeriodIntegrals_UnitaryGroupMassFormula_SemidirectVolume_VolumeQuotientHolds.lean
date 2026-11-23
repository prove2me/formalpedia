-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:59.372962+00:00
-- url     : https://prove2.me/theorems/620a6df8-c9e8-4522-aaf3-a08dad61b061
-- title:
--   Volume Quotient Holds
-- statement:
--   Definitions and structural lemmas for Volume Quotient Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolSemiDirect.W
open MeasureTheory
section Dec
variable {X : Type} [Group X] [TopologicalSpace X] {K N H : Subgroup X}
end Dec
def mkR {X : Type} [Group X] {Γ K : Subgroup X} (x : K) (hx : (x : X) ∈ Γ) : ratG Γ K :=
  ⟨x, Subgroup.mem_subgroupOf.2 ⟨hx, x.2⟩⟩
end PI.VolSemiDirect.W


