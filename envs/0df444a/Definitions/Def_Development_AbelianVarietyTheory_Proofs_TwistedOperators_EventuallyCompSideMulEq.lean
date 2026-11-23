-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_EventuallyCompSideMulEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:41:41.171924+00:00
-- url     : https://prove2.me/theorems/cb1e242d-d290-4d9a-a615-dd1827c5c319
-- title:
--   Eventually Comp Side Mul Eq
-- statement:
--   Definitions and structural lemmas for Eventually Comp Side Mul Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/EventuallyCompSideMulEq.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
namespace GlobalTheory.SplitWeil
section
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
end
end GlobalTheory.SplitWeil


