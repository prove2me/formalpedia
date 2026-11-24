-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndicatorBoxEqCharSum
-- name    : Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IndicatorBoxEqCharSum
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T22:21:58.380038+00:00
-- url     : https://prove2.me/theorems/0470350c-b000-42c1-9ed3-80e3acae4cfb
-- title:
--   Indicator Box Eq Char Sum
-- statement:
--   Definitions and structural lemmas for Indicator Box Eq Char Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/IndicatorBoxEqCharSum.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousCharactersLocallyConstantNonarchLocalF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_IsBicharPairing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix GlobalTheory.SplitWeil
open scoped Topology
noncomputable section
namespace GlobalTheory.BoxCharComb
open GlobalTheory.LocMod.Inhab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
end GlobalTheory.BoxCharComb


