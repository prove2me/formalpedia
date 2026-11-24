-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
-- name    : Development_AutomorphicSpectrum_Proofs_TwistedProofs_HeisenbergMatrixFacts
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T18:34:20.162355+00:00
-- url     : https://prove2.me/theorems/c17ace04-13a4-4bd4-a35e-09b21529dc7b
-- title:
--   Heisenberg Matrix Facts
-- statement:
--   Definitions and structural lemmas for Heisenberg Matrix Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/HeisenbergMatrixFacts.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
import Theorems.Thm_GlobalTheory_Doubling_val_aOf
import Theorems.Thm_GlobalTheory_Doubling_val_leviOf
import Theorems.Thm_GlobalTheory_InertZeta_blk_last
import Theorems.Thm_GlobalTheory_InertZeta_blk_mid
import Theorems.Thm_GlobalTheory_InertZeta_blk_zero
import Theorems.Thm_GlobalTheory_InertZeta_val_mid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] GlobalTheory.Doubling.flatSec_self
attribute [local simp] GlobalTheory.Doubling.val_aOf
attribute [local simp] GlobalTheory.Doubling.val_leviOf
attribute [local simp] GlobalTheory.InertZeta.blk_last
attribute [local simp] GlobalTheory.InertZeta.blk_mid
attribute [local simp] GlobalTheory.InertZeta.blk_zero
attribute [local simp] GlobalTheory.InertZeta.val_mid


set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
namespace GlobalTheory.CompanionTheory.InertHeis
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
section Entries
variable {u : GU σ (N + 2)}
end Entries
def ext (v : Fin N → L) : Fin (N + 2) → L := Fin.cons 0 (Fin.snoc (α := fun _ => L) v 0)
@[simp] theorem ext_zero (v : Fin N → L) : ext v 0 = 0 := rfl
@[simp] theorem ext_mid (v : Fin N → L) (j : Fin N) : ext v (mid j) = v j := by
  rw [GlobalTheory.CompanionTheory.InertHeis.ext, mid, Fin.cons_succ, Fin.snoc_castSucc]
@[simp] theorem ext_last (v : Fin N → L) : ext v (Fin.last (N + 1)) = 0 := by
  show Fin.cons (α := fun _ => L) (0 : L) (Fin.snoc (α := fun _ => L) v 0) (Fin.last N).succ = 0
  rw [Fin.cons_succ, Fin.snoc_last]
def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j + (if i = 0 then ext r j else 0) +
    (if j = Fin.last (N + 1) then ext b i else 0) + (if i = 0 ∧ j = Fin.last (N + 1) then c else 0)
section Values
variable (r b : Fin N → L) (c : L)
end Values
end GlobalTheory.CompanionTheory.InertHeis


