-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:58:12.614545+00:00
-- url     : https://prove2.me/theorems/4011cccb-3f74-4175-88a1-0e6463a75a9f
-- title:
--   Integral Mem Nhds And Subset Compact Of Finrank Two
-- statement:
--   Definitions and structural lemmas for Integral Mem Nhds And Subset Compact Of Finrank Two, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/IntegralMemNhdsAndSubsetCompactOfFinrankTwo.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_ExistsHaarOfSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Topology Polynomial
namespace PI.LocHaarRRW
section None
variable {K V : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [CharZero K] [CommRing V] [Algebra K V]
end None
end PI.LocHaarRRW


