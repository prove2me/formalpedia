-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAlternantRenamePlace
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAlternantRenamePlace
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:13.119901+00:00
-- url     : https://prove2.me/theorems/4fe6b09a-bd7b-4291-bdfe-cca2c8aa1984
-- title:
--   PSch Alternant Rename Place
-- statement:
--   Definitions and structural lemmas for PSch Alternant Rename Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAlternantRenamePlace.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
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
open MvPolynomial
noncomputable section
def smallBlockEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv := by
    intro x
    cases c <;> rcases x with i | j <;> simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv := by
    intro p
    cases c <;> simp only [smallBlockOf] <;> split_ifs with h <;>
      apply Fin.ext <;> simp [smallBlockPlace, yIndex, zIndex] <;> omega
end
end GroundTheory.Heights₂.Heights.RestTerms


