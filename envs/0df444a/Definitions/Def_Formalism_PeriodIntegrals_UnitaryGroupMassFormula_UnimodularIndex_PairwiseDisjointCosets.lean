-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularIndex_PairwiseDisjointCosets
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:02.81096+00:00
-- url     : https://prove2.me/theorems/578faae7-f1e2-4696-b586-d7eb3510637d
-- title:
--   Pairwise Disjoint Cosets
-- statement:
--   Definitions and structural lemmas for Pairwise Disjoint Cosets, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnimodularIndex/PairwiseDisjointCosets.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodIdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Pointwise Set Function
noncomputable section
namespace PI.UnimodIdxWork
section Cosets
variable {G : Type} [Group G]
end Cosets
section Measure
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G]
end Measure
end PI.UnimodIdxWork


