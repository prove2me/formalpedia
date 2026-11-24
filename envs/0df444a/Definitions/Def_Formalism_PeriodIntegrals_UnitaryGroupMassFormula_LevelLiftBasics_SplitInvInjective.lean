-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelLiftBasics_SplitInvInjective
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T13:50:53.828818+00:00
-- url     : https://prove2.me/theorems/4b1b11b6-5347-45a1-906e-e143290886fa
-- title:
--   Split Inv Injective
-- statement:
--   Definitions and structural lemmas for Split Inv Injective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelLiftBasics/SplitInvInjective.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace PI.QnLevBasicsW
open Formalism.QuantumDeterminants
def splitInv (k i r' : ℕ) : Fin (2 * r' + k + 1) ⊕ Fin (2 * i) → Fin (2 * (i + r') + k + 1)
  | Sum.inl a => ⟨a.val + i, by omega⟩
  | Sum.inr b => ⟨if b.val < i then b.val else b.val + (2 * r' + k + 1), by split_ifs <;> omega⟩
theorem splitInv_inl (k i r' : ℕ) (a : Fin (2 * r' + k + 1)) : (splitInv k i r' (Sum.inl a)).val = a.val + i := rfl
theorem splitInv_inr (k i r' : ℕ) (b : Fin (2 * i)) :
    (splitInv k i r' (Sum.inr b)).val = if b.val < i then b.val else b.val + (2 * r' + k + 1) := rfl
theorem splitInv_injective (k i r' : ℕ) : Function.Injective (splitInv k i r') := by
  intro x y h
  have hv := congrArg Fin.val h
  rcases x with a | b <;> rcases y with a' | b' <;> simp only [splitInv_inl, splitInv_inr] at hv
  · exact congrArg Sum.inl (Fin.ext (by omega))
  · have := a.isLt
    have := b'.isLt
    split_ifs at hv <;> omega
  · have := b.isLt
    have := a'.isLt
    split_ifs at hv <;> omega
  · have := b.isLt
    have := b'.isLt
    exact congrArg Sum.inr (Fin.ext (by split_ifs at hv <;> omega))
def split (k i r' : ℕ) : Fin (2 * (i + r') + k + 1) ≃ Fin (2 * r' + k + 1) ⊕ Fin (2 * i) :=
  (Equiv.ofBijective (splitInv k i r') ((Fintype.bijective_iff_injective_and_card _).2
    ⟨splitInv_injective k i r', by simp; omega⟩)).symm
variable {k i r' : ℕ}
def Jrest (k i r' : ℕ) : Matrix (Fin (2 * i)) (Fin (2 * i)) ℂ :=
  (Hpk k (i + r')).submatrix ((split k i r').symm ∘ Sum.inr) ((split k i r').symm ∘ Sum.inr)
end PI.QnLevBasicsW


