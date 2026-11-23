-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_LintegralMulAvgComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:19.612825+00:00
-- url     : https://prove2.me/theorems/cc381e42-fb88-42d6-9f88-e6e752c7d282
-- title:
--   Lintegral Mul Avg Comm
-- statement:
--   Definitions and structural lemmas for Lintegral Mul Avg Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilQuotientMeasure/LintegralMulAvgComm.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WeilQuotMeas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilQuotientMeasure_StepBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology
open scoped ENNReal Pointwise
namespace PI.WeilQuotMeas.UnitaryGroupMassFormula
section Lemmas
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G}
end Lemmas
end PI.WeilQuotMeas.UnitaryGroupMassFormula


