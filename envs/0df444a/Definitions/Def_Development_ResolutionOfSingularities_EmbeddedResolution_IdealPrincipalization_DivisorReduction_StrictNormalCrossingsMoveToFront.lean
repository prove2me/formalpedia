-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_IdealPrincipalization_DivisorReduction_StrictNormalCrossingsMoveToFront
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:31.022818+00:00
-- url     : https://prove2.me/theorems/28dd0904-9175-4632-9c6b-78f439208d0e
-- title:
--   Strict Normal Crossings Move To Front
-- statement:
--   Definitions and structural lemmas for Strict Normal Crossings Move To Front, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/IdealPrincipalization/DivisorReduction/StrictNormalCrossingsMoveToFront.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {α : Type*}
def moveToFront (E : List α) (j : ℕ) : List α :=
  match E[j]? with
  | some a => a :: E.eraseIdx j
  | none => E
theorem moveToFront_eq_cons (E : List α) (j : ℕ) (hj : j < E.length) :
    moveToFront E j = (E[j]'hj) :: E.eraseIdx j := by
  simp [moveToFront, List.getElem?_eq_getElem hj]
theorem length_moveToFront (E : List α) (j : ℕ) (hj : j < E.length) :
    (moveToFront E j).length = E.length := by
  rw [moveToFront_eq_cons E j hj, List.length_cons,
    List.length_eraseIdx_add_one hj]
def indexBeforeMoveToFront (j : ℕ) : ℕ → ℕ
  | 0 => j
  | (i + 1) => if i < j then i else i + 1
theorem indexBeforeMoveToFront_lt_length (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ)
    (hi : i < E.length) : indexBeforeMoveToFront j i < E.length := by
  cases i with
  | zero => exact hj
  | succ n =>
    show (if n < j then n else n + 1) < E.length
    split <;> omega
def indexInMoveToFront (j : ℕ) (i : ℕ) : ℕ := if i = j then 0 else if i < j then i + 1 else i
theorem indexInMoveToFront_lt_length (E : List α) (j : ℕ) (hj : j < E.length) (i : ℕ) (hi : i < E.length) :
    indexInMoveToFront j i < (moveToFront E j).length := by
  rw [length_moveToFront E j hj]
  show (if i = j then 0 else if i < j then i + 1 else i) < E.length
  split_ifs <;> omega
end FunctorialResolution.EmbeddedResolution


