-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_TwistSupportPeriodicLevels
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:40:57.343919+00:00
-- url     : https://prove2.me/theorems/8ef71e92-9969-5c36-b18d-4110a06b77d8
-- title:
--   Twist Support Periodic Levels
-- statement:
--   Definitions and structural lemmas for Twist Support Periodic Levels, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TwistSupportPeriodicLevels.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_NormalRepresentationLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice
namespace GlobalTheory.Proof.TwistSupportPeriodicLevels
section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r s s' : Type} [Fintype r] [DecidableEq r]
variable {ι ι' Y Y' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y']
end
end GlobalTheory.Proof.TwistSupportPeriodicLevels


