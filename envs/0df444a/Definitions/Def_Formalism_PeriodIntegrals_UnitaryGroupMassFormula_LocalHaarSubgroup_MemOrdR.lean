-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_MemOrdR
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_MemOrdR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:01:57.964018+00:00
-- url     : https://prove2.me/theorems/2a8b7ab3-4ffe-4faf-b3dd-9146af69edec
-- title:
--   Mem Ord R
-- statement:
--   Definitions and structural lemmas for Mem Ord R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalHaarSubgroup/MemOrdR.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocHaarRR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalHaarSubgroup_IntegralMemNhdsAndSubsetCompactOfFinrankTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory Topology IsDedekindDomain NumberField
namespace PI.LocHaarRRW
section Some
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)} {A : Formalism.MainNotions.S.Loc.LocAt F E sig p}
end Some
end PI.LocHaarRRW


