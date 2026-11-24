-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:37:10.547889+00:00
-- url     : https://prove2.me/theorems/62c05eb4-9b9a-4969-8581-44bad8c13b37
-- title:
--   Unitary Heisenberg Radical Coordinates
-- statement:
--   Definitions and structural lemmas for Unitary Heisenberg Radical Coordinates, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
namespace GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
def Shape (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (r b : Fin N → L) (c : L) : Prop :=
  M 0 0 = 1 ∧ (∀ j, M 0 (mid j) = r j) ∧ M 0 (Fin.last (N + 1)) = c ∧ (∀ i, M (mid i) 0 = 0) ∧
  (∀ i j, M (mid i) (mid j) = if i = j then 1 else 0) ∧ (∀ i, M (mid i) (Fin.last (N + 1)) = b i) ∧
  M (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, M (Fin.last (N + 1)) (mid j) = 0) ∧
  M (Fin.last (N + 1)) (Fin.last (N + 1)) = 1
def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  if i = j then 1
  else if i = 0 ∧ j = Fin.last (N + 1) then c
  else if h : i = 0 ∧ 0 < j.val ∧ j.val < N + 1 then r ⟨j.val - 1, by omega⟩
  else if h : j = Fin.last (N + 1) ∧ 0 < i.val ∧ i.val < N + 1 then b ⟨i.val - 1, by omega⟩
  else 0
end GlobalTheory.InertZeta.HeisCoord


