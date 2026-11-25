-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_InhabitantsComb
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T06:28:28.553494+00:00
-- url     : https://prove2.me/theorems/b064566b-32a1-475c-93be-fd7fe556206d
-- title:
--   Inhabitants Comb
-- statement:
--   Definitions and structural lemmas for Inhabitants Comb, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/InhabitantsComb.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset Equiv Comb
noncomputable section
def inhNumberingFun (p : youngCells (![2, 1] : Fin 2 → ℕ)) : Fin 3 :=
  if p.1 = (0, 0) then 0 else if p.1 = (0, 1) then 1 else 2
theorem inhNumberingFun_bijective : Function.Bijective inhNumberingFun := by
  unfold inhNumberingFun
  decide
theorem inh_card_two_one : (youngCells (![2, 1] : Fin 2 → ℕ)).card = 3 := by decide
def inhNumbering :
    youngCells (![2, 1] : Fin 2 → ℕ) ≃ Fin (youngCells (![2, 1] : Fin 2 → ℕ)).card :=
  (Equiv.ofBijective _ inhNumberingFun_bijective).trans (finCongr inh_card_two_one.symm)
end
end GroundTheory.Heights₂.Heights.RestTerms


