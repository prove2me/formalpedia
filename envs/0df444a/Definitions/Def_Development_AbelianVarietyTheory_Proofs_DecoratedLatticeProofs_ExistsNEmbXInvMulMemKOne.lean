-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNEmbXInvMulMemKOne
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNEmbXInvMulMemKOne
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:17:02.379148+00:00
-- url     : https://prove2.me/theorems/306c1f88-10f9-41ee-9d73-6da33dcd259a
-- title:
--   Exists NEmb XInv Mul Mem KOne
-- statement:
--   Definitions and structural lemmas for Exists NEmb XInv Mul Mem KOne, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsNEmbXInvMulMemKOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
namespace GlobalTheory.SymChain.SymData
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
end GlobalTheory.SymChain.SymData


