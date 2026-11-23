-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:39.817012+00:00
-- url     : https://prove2.me/theorems/bb0a7038-24ff-4da2-9c1e-581af528ff3b
-- title:
--   Mul Int Mat Mul
-- statement:
--   Definitions and structural lemmas for Mul Int Mat Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CompactGelfandAverage/MulIntMatMul.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
end
end PI.UnitaryGroupMassFormula.GelfCpt


