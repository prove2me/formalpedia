-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatSweepSmoothlyInduced
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:35.018623+00:00
-- url     : https://prove2.me/theorems/a9825921-63c2-4563-9e05-e614cd7e0653
-- title:
--   Schwartz Bruhat Sweep Smoothly Induced
-- statement:
--   Definitions and structural lemmas for Schwartz Bruhat Sweep Smoothly Induced, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SchwartzBruhatSweepSmoothlyInduced.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatEventuallyInvariantOfContinuousAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology Filter
namespace GlobalTheory.SBInduced
variable {G X Y : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace X]
  [TopologicalSpace Y]
end GlobalTheory.SBInduced


