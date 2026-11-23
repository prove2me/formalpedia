-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_LocallyConstantExtensionByZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:46.46503+00:00
-- url     : https://prove2.me/theorems/70f4d239-afcd-4990-81c6-fce4fb87d19f
-- title:
--   Locally Constant Extension By Zero
-- statement:
--   Definitions and structural lemmas for Locally Constant Extension By Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/LocallyConstantExtensionByZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OpenClosedSequences
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology
noncomputable section
namespace GlobalTheory.SBExtend
variable {X : Type} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [TotallyDisconnectedSpace X]
end GlobalTheory.SBExtend


