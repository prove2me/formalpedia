-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_CompactOpenSubgroupExhaustion
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T21:10:49.892797+00:00
-- url     : https://prove2.me/theorems/1ff290b4-ebbe-40fb-a4c6-249618fde2fc
-- title:
--   Compact Open Subgroup Exhaustion
-- statement:
--   Definitions and structural lemmas for Compact Open Subgroup Exhaustion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CompactOpenSubgroupExhaustion.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
namespace GlobalTheory.KSp.GoodSpace
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
def boxSub (n : Type) [Fintype n] [DecidableEq n] (s : Fˣ) : AddSubgroup (n → F) where
  carrier := box n s
  zero_mem' := fun i _ => by simp [cball]
  add_mem' := fun ha hb i _ => add_mem_cball (ha i trivial) (hb i trivial)
  neg_mem' := fun ha i _ => neg_mem_cball (ha i trivial)
end GlobalTheory.KSp.GoodSpace


