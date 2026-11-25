-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenAndRelIndexNeZero
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsOpenAndRelIndexNeZero
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:34:50.48304+00:00
-- url     : https://prove2.me/theorems/645411fd-1189-51bf-afe5-7985fa9f7f2b
-- title:
--   Is Open And Rel Index Ne Zero
-- statement:
--   Definitions and structural lemmas for Is Open And Rel Index Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsOpenAndRelIndexNeZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
namespace GlobalTheory.RootEx.LatOpen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {ι : Type}
end GlobalTheory.RootEx.LatOpen


