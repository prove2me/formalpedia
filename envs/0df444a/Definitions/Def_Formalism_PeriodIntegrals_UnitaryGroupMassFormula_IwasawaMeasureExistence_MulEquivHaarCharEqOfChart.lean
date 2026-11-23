-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MulEquivHaarCharEqOfChart
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IwasawaMeasureExistence_MulEquivHaarCharEqOfChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:15.162404+00:00
-- url     : https://prove2.me/theorems/c2c73c90-245e-4f17-9309-a4947edff516
-- title:
--   Mul Equiv Haar Char Eq Of Chart
-- statement:
--   Definitions and structural lemmas for Mul Equiv Haar Char Eq Of Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IwasawaMeasureExistence/MulEquivHaarCharEqOfChart.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.IwaMeasEx.MG
open MeasureTheory Measure Topology Set
open scoped ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]
variable {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  [IsTopologicalAddGroup Y] [LocallyCompactSpace Y]
end PI.IwaMeasEx.MG
end


