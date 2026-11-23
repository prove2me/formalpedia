-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsEquivFourierClassesPosConeSummand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:14.209842+00:00
-- url     : https://prove2.me/theorems/e66445d8-8d3b-4a40-8c1d-0f73b70dbf8c
-- title:
--   Exists Equiv Fourier Classes Pos Cone Summand
-- statement:
--   Definitions and structural lemmas for Exists Equiv Fourier Classes Pos Cone Summand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsEquivFourierClassesPosConeSummand.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_TraceDualDifferent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RepNeZero
import Theorems.Thm_GlobalTheory_SlopeTestRemainingChoices_EisFibre_rep_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
namespace GlobalTheory.Div.QFibre
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.SlopeTestRemainingChoices.EisFibre
variable {F : Type} [Field F] [NumberField F]
def toQ (𝔞 𝔟 : Frac F) (x : Σ β : NzCls 𝔟, posCone 𝔞 (rep β)) : Quotient (qRel 𝔞 𝔟) :=
  Quotient.mk _ ⟨(x.2.1, rep x.1), x.2.2.1, rep_mem x.1, x.2.2.2⟩
end GlobalTheory.Div.QFibre


