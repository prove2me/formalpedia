-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_BlockSum
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_BlockSum
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T10:36:24.840992+00:00
-- url     : https://prove2.me/theorems/fc0f3a83-6d47-5774-a8e1-bd431e276ea4
-- title:
--   Block Sum
-- statement:
--   Definitions and structural lemmas for Block Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/IrreducibleCharacterSeries/BlockSum.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ClassFnOfIsIrrChar
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_Formalism_L2_NT_IsTeich_injective
import Theorems.Thm_Formalism_L2_NT_offs_add_le
import Theorems.Thm_Formalism_L2_NT_offs_add_le_sum
import Theorems.Thm_PI_SerBridgeGLW_sum_card_fibers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply


set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
namespace PI.SerBridgeGLW
section Gen
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
end Gen
theorem sum_c_eq {r s : ℕ} (b : Fin r → Fin s) (c : Fin s → ℕ) (e : ∀ j, {i // b i = j} ≃ Fin (c j)) :
    ∑ j, c j = r := by
  rw [← sum_card_fibers b]
  exact Finset.sum_congr rfl fun j _ => by rw [Fintype.card_congr (e j), Fintype.card_fin]
section Perm
variable {r s : ℕ} (b : Fin r → Fin s) (c : Fin s → ℕ) (e : ∀ j, {i // b i = j} ≃ Fin (c j))
theorem e_val_eq (j : Fin s) (i : Fin r) (h : b i = j) : (e (b i) ⟨i, rfl⟩).val = (e j ⟨i, h⟩).val := by
  subst h; rfl
theorem block_membership_unique {j j' : Fin s} {x : ℕ} (h : IsBaseBlockVar c j x) (h' : IsBaseBlockVar c j' x) : j = j' := by
  unfold IsBaseBlockVar at h h'
  rcases lt_trichotomy j j' with hl | hl | hl
  · have := offs_add_le c hl; omega
  · exact hl
  · have := offs_add_le c hl; omega
def tauFun (i : Fin r) : Fin r :=
  ⟨offs c (b i) + (e (b i) ⟨i, rfl⟩).val, by
    have h1 := offs_add_le_sum c (b i)
    have h2 := (e (b i) ⟨i, rfl⟩).isLt
    rw [sum_c_eq b c e] at h1
    omega⟩
theorem block_membership_permutation (i : Fin r) : IsBaseBlockVar c (b i) (tauFun b c e i).val := by
  unfold IsBaseBlockVar tauFun
  have h2 := (e (b i) ⟨i, rfl⟩).isLt
  simp only
  omega
theorem tauFun_injective : Function.Injective (tauFun b c e) := by
  intro i i' h
  have hb : b i' = b i := block_membership_unique c (h ▸ block_membership_permutation b c e i') (block_membership_permutation b c e i)
  have hv : (e (b i) ⟨i, rfl⟩).val = (e (b i) ⟨i', hb⟩).val := by
    have h3 := congrArg Fin.val h
    unfold tauFun at h3
    simp only at h3
    rw [e_val_eq b c e (b i) i' hb, hb] at h3
    omega
  have h4 : e (b i) ⟨i, rfl⟩ = e (b i) ⟨i', hb⟩ := Fin.ext hv
  have h5 := congrArg Subtype.val ((e (b i)).injective h4)
  exact h5
def tau : Fin r ≃ Fin r :=
  Equiv.ofBijective (tauFun b c e) (Finite.injective_iff_bijective.mp (tauFun_injective b c e))
end Perm
end PI.SerBridgeGLW


