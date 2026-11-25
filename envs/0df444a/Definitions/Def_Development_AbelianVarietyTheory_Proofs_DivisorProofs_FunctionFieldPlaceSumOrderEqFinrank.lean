-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceSumOrderEqFinrank
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:51:44.349018+00:00
-- url     : https://prove2.me/theorems/bf024a6e-8c8c-46a9-b07a-df567308c371
-- title:
--   Function Field Place Sum Order Eq Finrank
-- statement:
--   Definitions and structural lemmas for Function Field Place Sum Order Eq Finrank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceSumOrderEqFinrank.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Theorems.Thm_GroundTheory_FunctionField_Place_ordHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.FunctionField.Place.ordHom_apply


set_option autoImplicit false
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
namespace GlobalTheory.Nef.FundId
variable {k F : Type} [Field k] [Field F] [Algebra k F]
noncomputable def toRing (v : Place k F) : GroundTheory.FunctionField.Place k F where
  ring := v.1.valuationSubring
  ne_top := by
    intro h
    obtain ⟨x, hx⟩ := v.2.1 (WithZero.exp 1)
    have hm : x ∈ v.1.valuationSubring := h ▸ ValuationSubring.mem_top _
    rw [Valuation.mem_valuationSubring_iff, hx, ← WithZero.exp_zero, WithZero.exp_le_exp] at hm
    omega
  algebraMap_mem c := by
    rw [Valuation.mem_valuationSubring_iff]
    by_cases hc : c = 0
    · simp [hc]
    · exact (v.2.2 c hc).le
end GlobalTheory.Nef.FundId


