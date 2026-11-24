-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:23.892135+00:00
-- url     : https://prove2.me/theorems/97b64efe-53a0-4009-96fc-1de4d2532e50
-- title:
--   Not Is Self Dual ETwo
-- statement:
--   Definitions and structural lemmas for Not Is Self Dual ETwo, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv


set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
namespace GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
def stdLat (K : Type) [Field K] [NumberField K] (n : ℕ) : Submodule (𝓞 K) (Fin n → K) :=
  Submodule.span (𝓞 K) (Set.range (Pi.basisFun K (Fin n)))
def wOne : DomWeight 2 := ⟨![1, 0], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩
end GlobalTheory.TestLat.Model


