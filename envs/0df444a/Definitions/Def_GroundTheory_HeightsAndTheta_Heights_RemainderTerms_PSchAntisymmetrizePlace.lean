-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAntisymmetrizePlace
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchAntisymmetrizePlace
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T18:23:16.725798+00:00
-- url     : https://prove2.me/theorems/9ef6040e-a429-43b2-9b99-dac7af078856
-- title:
--   PSch Antisymmetrize Place
-- statement:
--   Definitions and structural lemmas for PSch Antisymmetrize Place, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchAntisymmetrizePlace.lean

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
open MvPolynomial Finset
noncomputable section
def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega
end
end GroundTheory.Heights₂.Heights.RestTerms


